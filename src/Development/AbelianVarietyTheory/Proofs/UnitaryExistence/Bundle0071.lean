module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

theorem comp_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (hξ : ξ ≠ 0)
    (A B : Type) [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (EA : A → A → ℤ) (EB : B → B → ℤ) (io : A →ₗ[𝓞 E] (Fin n → E)) (hio : Function.Injective io)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (φ : B ≃ₗ[𝓞 E] Λ)
    (hL : (LinearMap.range io).FG) (hLs : Submodule.span E (LinearMap.range io : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hA : ∀ x y, ((EA x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * ∑ a, ∑ b, io x a * G a b * c (io y b)))
    (hB : ∀ x y, ((EB x y : ℤ) : ℚ) =
      Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)))
    (f : ℕ → A →ₗ[𝓞 E] B)
    (h1 : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e)
    (h2 : ∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)
    (h3 : ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ EB (f n a) (f n a') - EA a a') :
    ∃ g : GL (Fin n) (AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (AdLat.RA F E)).mulVec '' (AdLat.hat F (LinearMap.range io : Set (Fin n → E))) =
        (AdLat.hat F (Λ : Set (Fin n → E))) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ (AdLat.hat F (Λ : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ AdLat.fv F (io a) =
          AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c G x y := by
  let ψ : A ≃ₗ[𝓞 E] LinearMap.range io := LinearEquiv.ofInjective io hio
  have hψ : ∀ a, (ψ a : Fin n → E) = io a := fun a => rfl
  let f' : ℕ → (LinearMap.range io →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ψ.symm.toLinearMap
  have hf' : ∀ N a, f' N (ψ a) = φ (f N a) := fun N a => by simp [f']
  obtain ⟨g, hg1, hg2, hg3⟩ := AdLat.exists_adelic_matrix_of_tower F E n (LinearMap.range io) Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ψ.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add (f := _), map_nsmul]⟩)
    (fun N hN => by
      refine ⟨fun a => ?_, fun a' => ?_⟩
      · obtain ⟨a, rfl⟩ := ψ.surjective a
        rw [hf']
        constructor
        · rintro ⟨v, hv⟩
          obtain ⟨v, rfl⟩ := φ.surjective v
          obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨v, φ.injective (by rw [hv, map_nsmul])⟩
          exact ⟨ψ e, by rw [he, map_nsmul]⟩
        · rintro ⟨v, hv⟩
          obtain ⟨v, rfl⟩ := ψ.surjective v
          obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨v, ψ.injective (by rw [hv, map_nsmul])⟩
          exact ⟨φ e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, rfl⟩ := φ.surjective a'
        obtain ⟨a, e, he⟩ := (h2 N hN).2 b
        exact ⟨ψ a, φ e, by rw [hf', ← map_nsmul, ← map_add (f := _), ← he]⟩)
  refine ⟨g, hg1, fun N hN a => ?_, ?_⟩
  · obtain ⟨w, hw, h⟩ := hg2 N hN (ψ a)
    exact ⟨w, hw, by rw [← hf', ← h, hψ]⟩
  let J : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ ξ⁻¹ * FractionalIdeal.dual ℤ ℚ 1
  have hJ : ∀ z : E, (∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * ((s : E) * z)) = k) → z ∈ J := by
    intro z hz
    refine FractionalIdeal.mem_singleton_mul.2 ⟨ξ * z, ?_, by field_simp⟩
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
    intro a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := hz s
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk]
    congr 1
    change ξ * ((s : E) * z) = ξ * z * (s : E)
    ring
  have hsm : ∀ (s : 𝓞 E) (x y : Fin n → E), (∑ a, ∑ b, (s • x) a * G a b * c (y b)) =
      (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change ((s : E) * x a) * _ * _ = _
    ring
  refine hg3 c G J (fun x hx y hy => hJ _ fun s => ?_) (fun N hN x y => ?_)
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨y, hy⟩
    refine ⟨EB (s • a) b, ?_⟩
    rw [hB, map_smul, ha, hb, ← hsm]
    rfl
  · obtain ⟨a, rfl⟩ := ψ.surjective x
    obtain ⟨b, rfl⟩ := ψ.surjective y
    rw [hf', hf', hψ, hψ]
    have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hN'' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨(N : E)⁻¹ * ((∑ i, ∑ j, (φ (f N a) : Fin n → E) i * G i j * c ((φ (f N b) : Fin n → E) j)) -
      ∑ i, ∑ j, io a i * G i j * c (io b j)), hJ _ fun s => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := h3 N hN (s • a) b
      refine ⟨k, ?_⟩
      have hk' := congrArg (Int.cast : ℤ → ℚ) hk
      push_cast at hk'
      rw [hA, hB, map_smul, map_smul, map_smul, Submodule.coe_smul, hsm, hsm, ← map_sub] at hk'
      apply mul_left_cancel₀ hN''
      rw [← hk', ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
      congr 1
      field_simp
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN', add_sub_cancel]

theorem comp_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem comp_latG (D : D7) (V : HSp D) :
    (latG V 1).FG ∧ Submodule.span D.host.E (latG V 1 : Set (Fin V.rank → D.host.E)) = ⊤ ∧ ∀ g : GA D V,
      (latG V g : Set (Fin V.rank → D.host.E)) = AdLat.latOf D.host.F (finHom V g).1 (latG V 1) ∧
      (latGHat V g : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
        (finHom V g).1.mulVec '' (AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
  let e : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map e
  have hfg : L.FG := V.standardTuple_isLattice.fg.map e
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have h := congrArg (Submodule.map (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)))
      hfull
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  have hhat : latHat V = AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold latHat AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, e x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have h1 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ L, w = a • x} := by
    unfold latG gLat
    congr 1
    ext w
    have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L hfg hsp).1
    simp only [map_one, Units.val_one, Set.mem_setOf_eq, hhat, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
      SetLike.mem_coe, ← hc]
    rfl
  have hs := fun g : GA D V => AdLat.scale_latOf D.host.F D.host.E V.rank L (finHom V g) D.host.AA (latG V 1)
    hfg hsp (comp_AA_ne_zero D) h1
  refine ⟨(hs 1).2.2.1, (hs 1).2.2.2, fun g => ⟨?_, ?_⟩⟩
  · rw [← (hs g).1]
    unfold latG gLat
    rw [hhat]
    rfl
  · rw [← (hs g).2.1]
    unfold latGHat gLat
    rw [hhat]

theorem comp_mem_HR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (c : E ≃ₐ[F] E) (σ : E →ₐ[F] E) (hc : ∀ x, c x = σ x) (G : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (AdLat.RA F E))
    (hg : ∀ x y, AdLat.hermA c (-G.transpose) (g.1 *ᵥ x) (g.1 *ᵥ y) = AdLat.hermA c (-G.transpose) x y) :
    g ∈ HR (Af F) σ G := by
  have hc' : (c : E →ₐ[F] E) = σ := AlgHom.ext hc
  change Formalism.UG.cT _ _ * _ * _ = _
  ext i j
  have h := hg (Pi.single j 1) (Pi.single i 1)
  simp only [AdLat.hermA, AdLat.sg, hc', Matrix.mulVec_single_one, Matrix.col_apply, Matrix.neg_apply,
    Matrix.transpose_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj] at h
  simp only [Pi.single_apply, apply_ite (Algebra.TensorProduct.map (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) σ),
    map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simp only [Matrix.mul_apply, Formalism.UG.cT, JR, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change _ * (1 ⊗ₜ _) * _ = _ * _ * sigR _ σ _
  ring

theorem comp_sub_eq {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) : x - (x + N • e + N • w) = N • -(e + w) := by
  rw [smul_neg, smul_add]
  abel

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_algebraMap_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : R ⊗[F] E) (hz : sigR R σ z = z) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = z := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have h : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := by simp [sigR]
      rw [h, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT z
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← TensorProduct.smul_tmul', ← ht, hz, ← two_smul F z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_unit_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : (R ⊗[F] E)ˣ)
    (hz : sigR R σ (z : R ⊗[F] E) = z) :
    ∃ a : Rˣ, Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom a = z := by
  have hz' : sigR R σ ((z⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (z⁻¹ : (R ⊗[F] E)ˣ) := by
    apply z.isUnit.mul_left_cancel
    conv_lhs => rw [← hz, ← map_mul]
    simp
  obtain ⟨a, ha⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz
  obtain ⟨b, hb⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz'
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; simp)
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

theorem exists_root_of_norm_one {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ y, σ y ≠ y) (u : E) (hu : σ u * u = 1) : ∃ x : Eˣ, (x : E) = u * σ x := by
  by_cases h : 1 + u = 0
  · obtain ⟨y, hy⟩ := hne
    refine ⟨Units.mk0 (y - σ y) (sub_ne_zero.2 hy.symm), ?_⟩
    rw [Units.val_mk0, map_sub, hσ]
    linear_combination (y - σ y) * h
  · refine ⟨Units.mk0 (1 + u) h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination - hu

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem isDetRoot_laws : ∀ (D : D7) (V : HSp D), (∀ g : GA D V, ∃ x, IsDetRoot V g x) ∧ (∀ g x x', IsDetRoot V g x → IsDetRoot V g x' → ∃ a, x' = x * idF D a) ∧ (∀ γ ∈ GQ V, ∃ x : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom x)) ∧ ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x') := by
  intro D V
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  refine ⟨GlobalTheory.RecDict.exists_isDetRoot D V, ?_, ?_, ?_⟩
  · intro g x x' hx hx'
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    unfold IsDetRoot at hx hx'
    obtain ⟨a, ha⟩ := exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr (x⁻¹ * x') (by
      apply (x.isUnit.map (sigR (AF D.host.F) D.sp.cm.sig)).mul_left_cancel
      apply x.isUnit.mul_left_cancel
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel_left, mul_left_comm, ← Units.val_mul, mul_inv_cancel_left]
      linear_combination (sigR (AF D.host.F) D.sp.cm.sig (x' : AE D)) * hx -
        (sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hx')
    refine ⟨a, ?_⟩
    unfold idF
    rw [ha, mul_inv_cancel_left]
  · intro γ hγ
    obtain ⟨γ', -, hγ'⟩ := hγ
    have hdet : (Formalism.L2.Theta.mt V γ).det = incA D (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
      rw [RingHom.map_det]
      congr 1
      exact congrArg Units.val hγ'.symm
    have hc : ∀ y, cA D (incA D y) = incA D (D.sp.cm.sig y) := by
      intro y; simp [cA, sigR, inclR]
    have hinj : Function.Injective (incA D) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
    have hu := det_conj_mul V γ
    rw [hdet, hc, ← map_mul, ← map_one (incA D)] at hu
    obtain ⟨x, hx⟩ := exists_root_of_norm_one (D.sp.cm.sig : D.host.E →+* D.host.E) hσ
      (GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm) _ (hinj hu)
    refine ⟨x, ?_⟩
    have key : incA D (x : D.host.E) = (Formalism.L2.Theta.mt V γ).det * cA D (incA D (x : D.host.E)) := by
      rw [hdet, hc, ← map_mul]
      exact congrArg _ hx
    unfold IsDetRoot
    rw [Units.coe_map]
    exact key
  · exact isDetRoot_mul V

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem isTypeFn_of_enum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem exists_openChart_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  intro hS E _ _ _ H Dw l Xo c z
  classical
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_of_enum Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((_root_.GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have htan : ∀ τ i, IsTanAt x (u τ i) := fun τ i => hb.1 _
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  have hb' : TanBasis x (fun j => u (e j).1 (e j).2) := by
    have : (fun j => u (e j).1 (e j).2) = fun i => (v i).left ≫ m.cm.F := by
      funext j
      show (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hb
  have hbasis := (_root_.GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c R x u _ e htan heig).2 hb'
  obtain ⟨s, hsn⟩ := _root_.GlobalTheory.SecTransport.exists_sec_nonzero E H Dw l Xo R x o.t m.toSABMap th hth
  have hgen := _root_.GlobalTheory.Frames.secGen_of_secNZ hS E H Dw l Xo R x s hsn
  have hx : x ≫ Xo.s = sOf c R := by
    have h1 : x ≫ Xo.s = (jR ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (jR ≫ ·) pullback.condition
    rw [h1, hs, sOf]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  let y : FrPt Xo c R := ⟨x, hx, u, htan, heig, hbasis, s, hgen⟩
  obtain ⟨p, ⟨f⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 R hft hred
  obtain ⟨y₀, hy₀⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c R p.R f.symm.toAlgHom y
  have hiso : IsIso (spMap f.symm.toAlgHom.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map f.symm.toRingEquiv.toCommRingCatIso.hom))
  refine ⟨p, spMap f.symm.toAlgHom.toRingHom ≫ jR, y₀, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · rw [hy₀.1, Category.assoc]
  · rw [Category.assoc, hs]
    refine (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm.trans (congrArg Spec.map ?_)
    ext a
    exact f.symm.commutes a
  · obtain ⟨q', hq'⟩ := (spMap f.symm.toAlgHom.toRingHom).surjective q
    exact ⟨q', by rw [Scheme.Hom.comp_apply, hq', hq]⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNearOne
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_root_near_one : ∀ (D : D7), ∀ W ∈ 𝓝 (1 : (AE D)ˣ), ∃ N ∈ 𝓝 (1 : (AE D)ˣ), ∀ u ∈ N, (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (u : AE D) = 1 → ∃ x ∈ W, (x : AE D) = (u : AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by
  intro D
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  exact GlobalTheory.AdLat.RootNear.exists_root_near D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP

end GlobalTheory.Member
end

