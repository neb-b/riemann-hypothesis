module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtFixedNearOneCommutativeCentralizer
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.SqrtFixCent

theorem eq_mul_of_comm_mulRight {K A : Type} [Field K] [Ring A] [Algebra K A] (f : Module.End K A)
    (hf : ∀ y : A, LinearMap.mulRight K y * f = f * LinearMap.mulRight K y) (y : A) :
    f y = f 1 * y := by
  have h := congrArg (fun g : Module.End K A => g 1) (hf y)
  change f 1 * y = f (1 * y) at h
  rw [one_mul] at h
  exact h.symm

end GlobalTheory.SqrtFixCent

namespace GlobalTheory

theorem sqrt_fix_near_one_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  intro p _ v B _ _ _
  letI tB : TopologicalSpace B := moduleTopology (Qv v) B
  haveI : IsModuleTopology (Qv v) B := ⟨rfl⟩
  intro e σ _ hσe hσm hσ1
  let M : Subalgebra (Qv v) B := Subalgebra.centralizer (Qv v) {e}
  have hM : ∀ x : B, x ∈ M ↔ x * e = e * x := by
    intro x
    simp [M, Subalgebra.mem_centralizer_iff, eq_comm]
  haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
  letI : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  let d := Module.finrank (Qv v) M
  let bM := Module.finBasis (Qv v) M
  let Lm : M →ₐ[Qv v] Matrix (Fin d) (Fin d) (Qv v) :=
    (LinearMap.toMatrixAlgEquiv bM).toAlgHom.comp (Algebra.lmul (Qv v) M)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Subalgebra.toSubmodule M)
  let P : B →ₗ[Qv v] M := Submodule.linearProjOfIsCompl (Subalgebra.toSubmodule M) q hq
  have hP : ∀ x : M, P x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hq x
  let L : B →ₗ[Qv v] Matrix (Fin d) (Fin d) (Qv v) := Lm.toLinearMap ∘ₗ P
  have hLc : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hL1 : L 1 = 1 := by
    show Lm (P ((1 : M) : B)) = 1
    rw [hP, map_one]
  obtain ⟨W₀, hW₀, hW₀s⟩ := GlobalTheory.matrix_sqrt_near_one_ultrametric (Qv v) d (RingHom.id _) continuous_id
  refine ⟨L ⁻¹' W₀, hLc.continuousAt.preimage_mem_nhds (by rw [hL1]; exact hW₀), ?_⟩
  intro s hs hse hσs
  let sM : M := ⟨s, (hM s).2 hse⟩
  have hLs : L s = Lm sM := by
    show Lm (P (sM : B)) = Lm sM
    rw [hP]
  obtain ⟨R, hRR, hRc, -⟩ := hW₀s _ (show L s ∈ W₀ from hs)
  rw [hLs] at hRR hRc
  let T := LinearMap.toMatrixAlgEquiv bM
  let f : Module.End (Qv v) M := T.symm R
  have hTs : Lm sM = T (LinearMap.mulLeft (Qv v) sM) := rfl
  have hf : ∀ g : Module.End (Qv v) M, g * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * g →
      g * f = f * g := by
    intro g hg
    apply T.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    apply hRc
    rw [hTs, ← map_mul, ← map_mul, hg]
  have hff : f * f = LinearMap.mulLeft (Qv v) sM := by
    apply T.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hRR]
    exact hTs
  have hfy : ∀ y : M, f y = f 1 * y := by
    refine GlobalTheory.SqrtFixCent.eq_mul_of_comm_mulRight f fun y => (hf _ ?_)
    exact LinearMap.ext fun x => mul_assoc sM x y
  have hρρ : f 1 * f 1 = sM := by
    have h := LinearMap.congr_fun hff 1
    change f (f 1) = sM * 1 at h
    rw [hfy (f 1), mul_one] at h
    exact h
  let σM : Module.End (Qv v) M :=
    { toFun := fun x => ⟨σ x, (hM _).2 (hσe x ((hM x).1 x.2))⟩
      map_add' := fun x y => Subtype.ext (by show σ ((x : B) + y) = σ x + σ y; exact map_add σ _ _)
      map_smul' := fun c x => Subtype.ext (by show σ (c • (x : B)) = c • σ x; exact map_smul σ _ _) }
  have hσM : ∀ x : M, ((σM x : M) : B) = σ x := fun x => rfl
  have hcomm : σM * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * σM := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show σ ((sM : B) * x) = (sM : B) * σ x
    rw [hσm s x hse ((hM x).1 x.2), hσs]
  have hσ1M : σM 1 = 1 := Subtype.ext (by show σ ((1 : M) : B) = ((1 : M) : B); exact hσ1)
  have hσρ : σM (f 1) = f 1 := by
    have h := LinearMap.congr_fun (hf σM hcomm) 1
    change σM (f 1) = f (σM 1) at h
    rw [hσ1M] at h
    exact h
  refine ⟨((f 1 : M) : B), (hM _).1 (f 1).2, congrArg Subtype.val hσρ, congrArg Subtype.val hρρ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumTwoSidedMulEqMatrixUnitUnitaryDatum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

section DensityCentralizer

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
  [Algebra.IsCentral F C] [IsSimpleRing C]

theorem exists_sum_mul_mul_eq_matrixUnit (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (γ : C) (hγ : (minpoly F γ).natDegree = n)
    (L : Type) [Field L] (ι : L →+* C) (hιinj : Function.Injective ι)
    (hι : ∀ z : C, z * γ = γ * z ↔ ∃ w, ι w = z) (r : ℕ) (e : Fin r → C)
    (he : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) (i i' : Fin r) :
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  classical
  let S : Subalgebra F C := Subalgebra.centralizer F {γ}
  have memS : ∀ z : C, z ∈ S ↔ ∃ w, ι w = z := by
    intro z
    rw [← hι z]
    simp [S, Subalgebra.mem_centralizer_iff, eq_comm]
  have hιS : ∀ w, ι w ∈ S := fun w => (memS _).2 ⟨w, rfl⟩
  have hγS : γ ∈ S := (memS γ).2 ((hι γ).1 rfl)
  have hcomm : ∀ s t : C, s ∈ S → t ∈ S → s * t = t * s := by
    intro s t hs ht
    obtain ⟨a, rfl⟩ := (memS s).1 hs
    obtain ⟨b, rfl⟩ := (memS t).1 ht
    rw [← map_mul, ← map_mul, mul_comm]
  let j : L →+* S :=
    { toFun := fun w => ⟨ι w, hιS w⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hj : Function.Bijective j := by
    refine ⟨fun a b h => hιinj (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨w, hw⟩ := (memS s).1 s.2
    exact ⟨w, Subtype.ext hw⟩
  haveI : IsSimpleRing S := IsSimpleRing.of_ringEquiv (RingEquiv.ofBijective j hj) inferInstance
  let Φ : S ⊗[F] Cᵐᵒᵖ →ₐ[F] Module.End F C :=
    (AlgHom.mulLeftRight F C).comp (Algebra.TensorProduct.map S.val (AlgHom.id F Cᵐᵒᵖ))
  have hΦ : ∀ (s : S) (b : Cᵐᵒᵖ) (x : C), Φ (s ⊗ₜ b) x = (s : C) * x * b.unop := by
    intro s b x
    simp [Φ, AlgHom.mulLeftRight_apply]
  have hΦinj : Function.Injective Φ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Φ.toRingHom).resolve_right
      (not_subsingleton _)

  have hWl : ∀ t : S ⊗[F] Cᵐᵒᵖ, ∀ (s : S) (x : C), Φ t ((s : C) * x) = (s : C) * Φ t x := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => intro s x; simp
    | tmul a b =>
      intro s x
      rw [hΦ, hΦ, ← mul_assoc, hcomm _ _ a.2 s.2, mul_assoc, mul_assoc, mul_assoc]
    | add t u ht hu =>
      intro s x
      simp only [map_add (f := _), LinearMap.add_apply, ht, hu, mul_add]
  let W : Submodule F (Module.End F C) :=
    { carrier := {f | ∀ (s : S) (x : C), f ((s : C) * x) = (s : C) * f x}
      add_mem' := by
        intro a b ha hb s x
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha s x, hb s x, mul_add]
      zero_mem' := by intro s x; simp
      smul_mem' := by
        intro c f hf s x
        simp only [Set.mem_setOf_eq] at hf
        simp [hf s x, mul_smul_comm] }
  have hrange : LinearMap.range Φ.toLinearMap ≤ W := by
    rintro _ ⟨t, rfl⟩
    exact hWl t

  let θ : (Fin r → S) →ₗ[F] C :=
    { toFun := fun β => ∑ k, (β k : C) * e k
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [Finset.smul_sum, smul_mul_assoc] }
  have hθ : ∀ β, θ β = ∑ k, (β k : C) * e k := fun β => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    let wa : Fin r → L := fun k => ((memS _).1 (a k).2).choose
    let wb : Fin r → L := fun k => ((memS _).1 (b k).2).choose
    have hwa : ∀ k, ι (wa k) = a k := fun k => ((memS _).1 (a k).2).choose_spec
    have hwb : ∀ k, ι (wb k) = b k := fun k => ((memS _).1 (b k).2).choose_spec
    have h1 : θ a = ∑ k, ι (wa k) * e k := by simp [hθ, hwa]
    have h2 : θ a = ∑ k, ι (wb k) * e k := by rw [hab]; simp [hθ, hwb]
    have := (he (θ a)).unique h1 h2
    funext k
    apply Subtype.ext
    rw [← hwa, ← hwb, this]
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, hc, -⟩ := he x
    exact ⟨fun k => ⟨ι (c k), hιS _⟩, by simp [hθ, hc]⟩
  let θe : (Fin r → S) ≃ₗ[F] C := LinearEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have hθe : ∀ β, θe β = ∑ k, (β k : C) * e k := fun β => rfl
  have hθsmul : ∀ (s : S) (x : C), θe.symm ((s : C) * x) = fun k => s * θe.symm x k := by
    intro s x
    rw [θe.symm_apply_eq, hθe]
    conv_lhs => rw [← θe.apply_symm_apply x, hθe]
    simp [Finset.mul_sum, mul_assoc]

  have hdimC : Module.finrank F C = r * Module.finrank F S := by
    rw [← θe.finrank_eq, Module.finrank_pi_fintype]
    simp
  have hdS : n ≤ Module.finrank F S := by
    let γS : S := ⟨γ, hγS⟩
    have hmin : minpoly F γS = minpoly F γ := by
      have := minpoly.algHom_eq S.val Subtype.val_injective γS
      simpa [γS] using this.symm
    have := (linearIndependent_pow (K := F) γS).fintype_card_le_finrank
    simpa [hmin, hγ] using this
  have hsrc : Module.finrank F (S ⊗[F] Cᵐᵒᵖ) = Module.finrank F S * n ^ 2 := by
    rw [Module.finrank_tensorProduct, MulOpposite.finrank, hC]
  have hrk : Module.finrank F (LinearMap.range Φ.toLinearMap) = Module.finrank F S * n ^ 2 := by
    rw [LinearMap.finrank_range_of_inj hΦinj, hsrc]
  let Ψ : W →ₗ[F] (Fin r → Fin r → S) :=
    { toFun := fun f k => θe.symm ((f : Module.End F C) (e k))
      map_add' := by intro a b; funext k; simp
      map_smul' := by intro c a; funext k; simp }
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfe : ∀ k, (f : Module.End F C) (e k) = 0 := by
      intro k
      have := congrFun hf k
      simpa [Ψ] using this
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨c, hc, -⟩ := he x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    have hfW := f.2
    simp only [W, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hfW
    simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [show ι (c k) = ((⟨ι (c k), hιS _⟩ : S) : C) from rfl, hfW, hfe, mul_zero]
  have hW : Module.finrank F W ≤ r * (r * Module.finrank F S) := by
    have := LinearMap.finrank_le_finrank_of_injective hΨ
    simpa [Module.finrank_pi_fintype] using this
  have hrn : r ≤ n := by
    have h1 : r * n ≤ n * n := by
      calc r * n ≤ r * Module.finrank F S := Nat.mul_le_mul_left _ hdS
        _ = n * n := by rw [← hdimC, hC, sq]
    exact Nat.le_of_mul_le_mul_right h1 hn
  have hWeq : LinearMap.range Φ.toLinearMap = W := by
    apply Submodule.eq_of_le_of_finrank_le hrange
    rw [hrk]
    refine hW.trans ?_
    calc r * (r * Module.finrank F S) ≤ n * (n * Module.finrank F S) :=
          Nat.mul_le_mul hrn (Nat.mul_le_mul_right _ hrn)
      _ = Module.finrank F S * n ^ 2 := by ring

  let E : Module.End F C :=
    LinearMap.mulRight F (e i) ∘ₗ (S.val.toLinearMap ∘ₗ
      ((LinearMap.proj i' : (Fin r → S) →ₗ[F] S) ∘ₗ θe.symm.toLinearMap))
  have hE : ∀ x, E x = (θe.symm x i' : C) * e i := fun x => rfl
  have hEW : E ∈ W := by
    intro s x
    rw [hE, hE, hθsmul]
    simp [mul_assoc]
  rw [← hWeq] at hEW
  obtain ⟨t, ht⟩ := hEW
  have hrep : ∀ t : S ⊗[F] Cᵐᵒᵖ, ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → C),
      ∀ x, Φ t x = ∑ k, ι (l k) * x * c k := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | tmul a b =>
      obtain ⟨w, hw⟩ := (memS a).1 a.2
      exact ⟨1, fun _ => w, fun _ => b.unop, by intro x; simp [hΦ, hw]⟩
    | add t u ht hu =>
      obtain ⟨N₁, l₁, c₁, h₁⟩ := ht
      obtain ⟨N₂, l₂, c₂, h₂⟩ := hu
      exact ⟨N₁ + N₂, Fin.append l₁ l₂, Fin.append c₁ c₂, by
        intro x; simp [Fin.sum_univ_add, h₁, h₂]⟩
  obtain ⟨N, l, c, hlc⟩ := hrep t
  refine ⟨N, l, c, fun β => ?_⟩
  set x := ∑ i'', ι (β i'') * e i'' with hx
  have hsym : θe.symm x = fun k => ⟨ι (β k), hιS _⟩ := by
    rw [θe.symm_apply_eq, hθe]
  rw [← hlc, show Φ t x = E x from congrArg (fun f => f x) ht, hE, hsym]

end DensityCentralizer

theorem exists_sum_mul_mul_eq_matrixUnit_htGroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (r : ℕ) (e : Fin r → G.C),
    (∀ x : G.C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) → ∀ i i' : Fin r,
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → G.C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  intro p _ G γ hγ L _ _ ι hinj hι r e he i i'
  exact exists_sum_mul_mul_eq_matrixUnit G.n G.n_pos G.rankC (γ : G.C) hγ L ι.toRingHom hinj hι r e he i i'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeftBasisCoordsAdicCompletion
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.LeftBasisBC

theorem existsUnique_coords_baseChange (K : Type) [CommRing K] [Algebra ℚ K]
    (L : Type) [Field L] [Algebra ℚ L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (h : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i)
    (y : K ⊗[ℚ] C) :
    ∃! β : Fin r → K ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (β i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
  let φ : (Fin r → L) →ₗ[ℚ] C :=
    { toFun := fun c => ∑ i, ι (c i) * e i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun q a => by simp [Finset.smul_sum] }
  have hφ : Function.Bijective φ := by
    rw [Function.bijective_iff_existsUnique]
    intro x
    obtain ⟨c, hc, hu⟩ := h x
    exact ⟨c, hc.symm, fun d hd => hu d hd.symm⟩
  let E : (Fin r → L) ≃ₗ[ℚ] C := LinearEquiv.ofBijective φ hφ
  let P : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] (Fin r → K ⊗[ℚ] L) :=
    TensorProduct.piRight ℚ ℚ K (fun _ : Fin r => L)
  let F : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] K ⊗[ℚ] C := TensorProduct.congr (LinearEquiv.refl ℚ K) E
  have key : ∀ z : K ⊗[ℚ] (Fin r → L), F z =
      ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (P z i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp [F, P, E, φ, TensorProduct.tmul_sum]
    | add a b ha hb =>
      simp only [map_add (f := _), ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  refine ⟨P (F.symm y), ?_, ?_⟩
  · show y = _
    rw [← key, LinearEquiv.apply_symm_apply]
  · intro β hβ
    have h1 := key (P.symm β)
    rw [LinearEquiv.apply_symm_apply, ← hβ] at h1
    rw [← h1, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem existsUnique_coords_adicCompletion :
    ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] C),
    ∃! β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) :=
  fun L _ _ C _ _ ι r e h v y =>
    existsUnique_coords_baseChange (v.adicCompletion ℚ) L C ι r e h y

end GlobalTheory.LeftBasisBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLoca
section
noncomputable section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem finiteAdeleRingAway_ext {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  Subtype.ext (funext h)

theorem exists_afP (s : ∀ v : AwayP p, Qv v)
    (hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), s v ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ t : AfP p, ∀ v, AfP.eval v t = s v :=
  ⟨(⟨s, hs⟩ : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]), fun _ => rfl⟩

variable (G : HTGroup p)

abbrev basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

abbrev mapV (v : AwayP p) : AfP p ⊗[ℚ] G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)

theorem repr_mapV (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (mapV G v z) i = AfP.eval v ((basA G).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp [basV, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem eq_of_mapV {z z' : AfP p ⊗[ℚ] G.C} (h : ∀ v, mapV G v z = mapV G v z') : z = z' :=
  (basA G).ext_elem fun i => finiteAdeleRingAway_ext fun v => by rw [← repr_mapV, ← repr_mapV, h v]

theorem exists_of_local (y : ∀ v : AwayP p, Qv v ⊗[ℚ] G.C)
    (hy : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v (y v)) :
    ∃ z : AfP p ⊗[ℚ] G.C, ∀ v, mapV G v z = y v := by
  choose a ha using fun i : Fin (Module.finrank ℚ G.C) =>
    exists_afP (fun v => (basV G v).repr (y v) i) (hy.mono fun v hv => hv i)
  refine ⟨(basA G).equivFun.symm a, fun v => (basV G v).ext_elem fun i => ?_⟩
  rw [repr_mapV, ← ha i v]
  congr 1
  exact congrFun ((basA G).equivFun.apply_symm_apply a) i

theorem mapV_star (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) :
    (starT G.star (Qv v) (mapV G v z)).unop = mapV G v (starT G.star (AfP p) z).unop := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      starT_tmul]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem mapV_algebraMap (v : AwayP p) (s : AfP p) :
    mapV G v (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (AfP.eval v s) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem exists_glue : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (h : ∀ v : AwayP p, Gv G v),
    (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), h v ∈ IntV G v) → ∃ g : G.GAf, ∀ v, piV G v g = h v := by
  intro p _ G h hint
  obtain ⟨X, hX⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ)) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.1)
  obtain ⟨Y, hY⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.2.1)
  obtain ⟨s, hs⟩ := exists_afP (fun v => (((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.1)
  obtain ⟨s', hs'⟩ := exists_afP (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.2)
  have hXY : X * Y = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.mul_inv]
  have hYX : Y * X = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.inv_mul]
  have hss : s * s' = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.mul_inv]
  have hss' : s' * s = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.inv_mul]
  let U : (AfP p ⊗[ℚ] G.C)ˣ := ⟨X, Y, hXY, hYX⟩
  let c : (AfP p)ˣ := ⟨s, s', hss, hss'⟩
  have hmem : (U, c) ∈ UPts G.star (AfP p) := by
    show X * (starT G.star (AfP p) X).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s
    refine eq_of_mapV G fun v => ?_
    rw [map_mul, ← mapV_star, hX, mapV_algebraMap, hs]
    exact (h v).2
  refine ⟨⟨(U, c), hmem⟩, fun v => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact hX v
  · apply Units.ext
    exact hs v

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicIntegersQuotPrimePowOfFiniteDimStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] (m : ℕ), Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  first | (exact @GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (exact GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow) | (intros; apply GlobalTheory.LKLoc.IntFin.finite_intK_quot_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicTensorUnramifiedIntegersQuotPrimePowStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ), Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) → Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) → Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  first | (exact @GlobalTheory.TenFin.finite_intKQ_quot) | (exact GlobalTheory.TenFin.finite_intKQ_quot) | (intros; apply GlobalTheory.TenFin.finite_intKQ_quot  <;> assumption)
end

