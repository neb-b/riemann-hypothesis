module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenSmulAndSelf
section
open Polynomial

namespace GlobalTheory

theorem finite_quot_span_singleton_of_dvr_sandwich (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [hF : Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hp
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  rw [hn, ← Ideal.span_singleton_pow, ← hm]
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := hF
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_submodules_between_smul_and_self :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  intro O A _ _ _ _ _ _ C hC c hc
  haveI := finite_quot_span_singleton_of_dvr_sandwich O c hc
  haveI : Module.Finite O C := Module.Finite.iff_fg.mpr hC
  let K : Submodule O C := (Ideal.span {c}) • (⊤ : Submodule O C)
  haveI : Finite (C ⧸ K) := Submodule.finite_quotient_smul (Ideal.span {c}) Module.Finite.fg_top
  let f : Submodule O A → Set (C ⧸ K) := fun N => K.mkQ '' {x : C | (x : A) ∈ N}
  have key : ∀ N M : Submodule O A, (N ≤ C ∧ ∀ x ∈ C, c • x ∈ N) → (M ≤ C ∧ ∀ x ∈ C, c • x ∈ M) →
      f N = f M → N ≤ M := by
    intro N M hN hM h x hx
    have h1 : K.mkQ ⟨x, hN.1 hx⟩ ∈ f M := h ▸ ⟨⟨x, hN.1 hx⟩, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h1
    have h2 : y - ⟨x, hN.1 hx⟩ ∈ K := (Submodule.Quotient.eq K).mp hxy
    have h3 : ∀ z ∈ K, (z : A) ∈ M := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [Submodule.coe_smul, mul_smul]
        exact M.smul_mem a (hM.2 n n.2)
      · intro a b ha hb
        exact M.add_mem ha hb
    have h4 := M.sub_mem hy (h3 _ h2)
    simpa using h4
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro N hN M hM h
  exact le_antisymm (key N M hN hM h) (key M N hM hN h.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddFinrankLeFinrankInfComapSubId
section
open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_finrank_le_finrank_inf_comap_sub_id :
    ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  intro k _ M W _ _ _ _ D R _ F B hRD hFD hBR hBF hnd

  let RV : Submodule k ↥D := R.comap D.subtype
  let T : ↥D →ₗ[k] ↥D := F.restrict hFD - LinearMap.id
  let Q : ↥D →ₗ[k] ↥D ⧸ RV := RV.mkQ ∘ₗ T

  let P : W →ₗ[k] Module.Dual k ↥D := (B ∘ₗ D.subtype).flip
  have hP : ∀ w, P w ∈ RV.dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hBR x.1 hx w
  let L : W →ₗ[k] Module.Dual k (↥D ⧸ RV) :=
    RV.dualCopairing ∘ₗ P.codRestrict RV.dualAnnihilator hP
  have hL : ∀ w (x : ↥D), L w (RV.mkQ x) = B x.1 w := fun _ _ => rfl

  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply hnd
    intro x hx
    have h := LinearMap.congr_fun hw (RV.mkQ ⟨x, hx⟩)
    rw [hL, LinearMap.zero_apply] at h
    exact h

  have hLQ : ∀ w, L w ∈ (LinearMap.range Q).dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨x, rfl⟩
    have hTx : ((T x : ↥D) : M) = F x.1 - x.1 := rfl
    show L w (RV.mkQ (T x)) = 0
    rw [hL, hTx, map_sub, LinearMap.sub_apply, hBF x.1 x.2, sub_self]
  have hW : finrank k W ≤ finrank k (LinearMap.range Q).dualAnnihilator :=
    LinearMap.finrank_le_finrank_of_injective (f := L.codRestrict _ hLQ)
      (fun a b h => hLinj (congrArg Subtype.val h))

  have hker : LinearMap.ker Q = (D ⊓ R.comap (F - LinearMap.id)).comap D.subtype := by
    ext x
    constructor
    · intro h
      have h' : T x ∈ RV := (Submodule.Quotient.mk_eq_zero RV).mp h
      exact ⟨x.2, h'⟩
    · intro h
      exact (Submodule.Quotient.mk_eq_zero RV).mpr h.2
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range Q)
  have h2 := Submodule.finrank_quotient_add_finrank RV
  have h3 := LinearMap.finrank_range_add_finrank_ker Q
  have h4 : finrank k ↥RV = finrank k ↥R := (Submodule.comapSubtypeEquivOfLe hRD).finrank_eq
  have h5 : finrank k ↥(LinearMap.ker Q) = finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddLeFinrankRangeAddOfComapLe
section
open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_le_finrank_range_add_of_comap_le : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  intro k _ E A M _ _ _ _ _ _ π ν Z R U _ _ hZ hRU hU hmap
  set Q := LinearMap.range π with hQ
  set Z' : Submodule k Q := Z.comap Q.subtype
  set R' : Submodule k U := R.comap U.subtype
  have hZ' : finrank k Z' = finrank k Z := (Submodule.comapSubtypeEquivOfLe hZ).finrank_eq
  have hR' : finrank k R' = finrank k R := (Submodule.comapSubtypeEquivOfLe hRU).finrank_eq
  set K : Submodule k E := U.comap ν
  let g : K →ₗ[k] Q ⧸ Z' := Z'.mkQ ∘ₗ π.rangeRestrict ∘ₗ K.subtype
  let f : K →ₗ[k] U ⧸ R' := R'.mkQ ∘ₗ ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨u, rfl⟩ := R'.mkQ_surjective y
    obtain ⟨e, he⟩ := hU u.2
    have heU : ν e ∈ U := he ▸ u.2
    refine ⟨⟨e, heU⟩, ?_⟩
    have hu : ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) ⟨e, heU⟩ = u := Subtype.ext he
    exact congrArg R'.mkQ hu
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    have h0 : Submodule.Quotient.mk (p := Z') (π.rangeRestrict (x : E)) = 0 := LinearMap.mem_ker.mp hx
    have hx' : π (x : E) ∈ Z := (Submodule.Quotient.mk_eq_zero (p := Z')).mp h0
    have hy : ν (x : E) ∈ R := hmap _ hx'
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero (p := R')
      (x := ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) x)).mpr hy
  let gq := (LinearMap.ker g).liftQ g le_rfl
  let fq := (LinearMap.ker g).liftQ f hker
  have hgq : Function.Injective gq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfq : Function.Surjective fq := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have : Module.Finite k (K ⧸ LinearMap.ker g) := Module.Finite.of_injective gq hgq
  have key : finrank k (U ⧸ R') ≤ finrank k (Q ⧸ Z') :=
    (LinearMap.finrank_le_finrank_of_surjective hfq).trans
      (LinearMap.finrank_le_finrank_of_injective hgq)
  have h1 := Submodule.finrank_quotient_add_finrank R'
  have h2 := Submodule.finrank_quotient_add_finrank Z'
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAnnihilatorAdd
section
open Module

namespace GlobalTheory.HyodoDef.PairLin

variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']

theorem finrank_annihilator_add (β : M →ₗ[k] M' →ₗ[k] k) (S : Submodule k M')
    (hS : LinearMap.ker β.flip ≤ S) :
    finrank k (LinearMap.ker (S.subtype.dualMap ∘ₗ β)) + finrank k S
      = finrank k M + finrank k (LinearMap.ker β.flip) := by
  set φ : M →ₗ[k] Dual k S := S.subtype.dualMap ∘ₗ β with hφ
  set ψ : S →ₗ[k] Dual k M := β.flip ∘ₗ S.subtype with hψ
  have hφψ : φ = ψ.dualMap ∘ₗ (Module.evalEquiv k M).toLinearMap := by
    ext a s; rfl
  have hrange : LinearMap.range φ = LinearMap.range ψ.dualMap := by
    rw [hφψ, LinearEquiv.range_comp]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank k (LinearMap.range φ) = finrank k (LinearMap.range ψ) := by
    rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h4 : finrank k (LinearMap.ker ψ) = finrank k (LinearMap.ker β.flip) := by
    have : LinearMap.ker ψ = (LinearMap.ker β.flip).comap S.subtype := by
      rw [hψ, LinearMap.ker_comp]
    rw [this]
    exact (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  omega

theorem finrank_add_le (β : M →ₗ[k] M' →ₗ[k] k) (Ag Af : Submodule k M) (Ae Af' : Submodule k M')
    (hN : ∀ b : M', (∀ a : M, β a b = 0) → b ∈ Ae ⊓ Af')
    (hg : ∀ a ∈ Ag, ∀ b ∈ Ae, β a b = 0)
    (hf : ∀ a : M, a ∈ Af ↔ ∀ b ∈ Af', β a b = 0) :
    finrank k Ag + finrank k Ae ≤ finrank k Af + finrank k Af' := by
  have hker : ∀ b : M', b ∈ LinearMap.ker β.flip → b ∈ Ae ⊓ Af' := by
    intro b hb
    apply hN b
    intro a
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hb) a
    simpa using this
  have hNe : LinearMap.ker β.flip ≤ Ae := fun b hb => (hker b hb).1
  have hNf : LinearMap.ker β.flip ≤ Af' := fun b hb => (hker b hb).2
  have he := finrank_annihilator_add β Ae hNe
  have hf' := finrank_annihilator_add β Af' hNf
  have hgle : Ag ≤ LinearMap.ker (Ae.subtype.dualMap ∘ₗ β) := by
    intro a ha
    rw [LinearMap.mem_ker]
    ext ⟨b, hb⟩
    simpa using hg a ha b hb
  have hfeq : Af = LinearMap.ker (Af'.subtype.dualMap ∘ₗ β) := by
    ext a
    rw [hf a, LinearMap.mem_ker]
    constructor
    · intro h
      ext ⟨b, hb⟩
      simpa using h b hb
    · intro h b hb
      have := LinearMap.congr_fun h ⟨b, hb⟩
      simpa using this
  have hAg := Submodule.finrank_mono hgle
  rw [hfeq]
  omega

end GlobalTheory.HyodoDef.PairLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankEqOfNondegenerate
section
namespace GlobalTheory.NondegenerateFinrank

theorem finrank_eq_of_nondegenerate {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (h1 : ∀ (x : V), (∀ (y : V'), P x y = 0) → x = 0)
    (h2 : ∀ (y : V'), (∀ (x : V), P x y = 0) → y = 0) :
    Module.finrank LL V = Module.finrank LL V' := by
  have i1 : Function.Injective P := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact h1 x (fun y => by simp [hx])
  have i2 : Function.Injective P.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y (fun x => by
      have := LinearMap.congr_fun hy x
      simpa using this)
  have a := LinearMap.finrank_le_finrank_of_injective i1
  have b := LinearMap.finrank_le_finrank_of_injective i2
  have ea : Module.finrank LL (V' →ₗ[LL] LL) = Module.finrank LL V' := Subspace.dual_finrank_eq
  have eb : Module.finrank LL (V →ₗ[LL] LL) = Module.finrank LL V := Subspace.dual_finrank_eq
  omega

theorem main : ∀ {LL : Type} [inst : Field LL] {V V' : Type} [inst_1 : AddCommGroup V] [inst_2 : Module LL V] [FiniteDimensional LL V] [inst_4 : AddCommGroup V'] [inst_5 : Module LL V'] [FiniteDimensional LL V'] (P : V →ₗ[LL] V' →ₗ[LL] LL), (∀ (x : V), (∀ (y : V'), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → x = (0 : V)) → (∀ (y : V'), (∀ (x : V), ((P : V → V' →ₗ[LL] LL) x : V' → LL) y = (0 : LL)) → y = (0 : V')) → Module.finrank LL V = Module.finrank LL V' :=
  fun P h1 h2 => finrank_eq_of_nondegenerate P h1 h2

end GlobalTheory.NondegenerateFinrank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrix
section
open TensorProduct Module

open Matrix

theorem GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  intro F E _ _ _ _ B _ _ _ _ _ G act n _ _ A hfix Q hQ W hW
  set Q' : Matrix n n B := (Q : Matrix n n B) with hQ'
  have hQQ' : (↑Q⁻¹ : Matrix n n B) * Q' = 1 := by rw [hQ']; exact_mod_cast Q.inv_mul
  have hQQ : Q' * (↑Q⁻¹ : Matrix n n B) = 1 := by rw [hQ']; exact_mod_cast Q.mul_inv
  have key : ∀ g (y : n → B), (A g).mulVec (fun i => act g ((Q' *ᵥ y) i)) = Q' *ᵥ (fun i => act g (y i)) := by
    intro g y
    have h1 : (fun i => act g ((Q' *ᵥ y) i)) = Q'.map (act g) *ᵥ (fun i => act g (y i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ _
    rw [h1, Matrix.mulVec_mulVec, hQ g]
  have inj : ∀ u v : n → B, Q' *ᵥ u = Q' *ᵥ v → u = v := by
    intro u v h
    have h2 := congrArg (fun w => (↑Q⁻¹ : Matrix n n B) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec] at h2
    rwa [hQQ', Matrix.one_mulVec, Matrix.one_mulVec] at h2
  let φ : (n → E) →ₗ[F] (n → B) :=
    { toFun := fun c => Q' *ᵥ (fun i => algebraMap E B (c i))
      map_add' := by
        intro a b
        have : (fun i => algebraMap E B ((a + b) i)) = (fun i => algebraMap E B (a i)) + (fun i => algebraMap E B (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add]
      map_smul' := by
        intro r a
        have : (fun i => algebraMap E B ((r • a) i)) = r • (fun i => algebraMap E B (a i)) := by
          funext i
          simp only [Pi.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
        rw [this, Matrix.mulVec_smul]
        rfl }
  have hφ : ∀ c, φ c = Q' *ᵥ (fun i => algebraMap E B (c i)) := fun c => rfl
  have φinj : Function.Injective φ := by
    intro a b h
    rw [hφ, hφ] at h
    have h3 := inj _ _ h
    funext i
    exact (algebraMap E B).injective (congrFun h3 i)
  have hWr : W = LinearMap.range φ := by
    ext x
    rw [hW, LinearMap.mem_range]
    constructor
    · intro hx
      set y : n → B := (↑Q⁻¹ : Matrix n n B) *ᵥ x with hy
      have hxy : Q' *ᵥ y = x := by rw [hy, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
      have hfixy : ∀ i g, act g (y i) = y i := by
        intro i g
        have h4 := hx g
        rw [← hxy, key] at h4
        exact congrFun (inj _ _ h4) i
      choose c hc using fun i => (hfix (y i)).1 (hfixy i)
      refine ⟨c, ?_⟩
      rw [hφ, ← hxy]
      congr 1
      funext i; exact hc i
    · rintro ⟨c, rfl⟩ g
      rw [hφ, key]
      congr 1
      funext i
      exact ((hfix _).2 ⟨c i, rfl⟩) g
  subst hWr
  rw [LinearMap.finrank_range_of_inj φinj, Module.finrank_pi_fintype]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKerMapLeOfFirstOrderKernelExt
section
open Polynomial
namespace GlobalTheory
theorem finrank_le_of_first_order_kernel (k V U : Type) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup U] [Module k U] [Module.Finite k U] (e : ℕ) (t u : V →ₗ[k] U)
    (h : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) :
    Module.finrank k V ≤ Module.finrank k U + e := by
  classical
  set q : LinearMap.ker t →ₗ[k] U ⧸ LinearMap.range t :=
    (LinearMap.range t).mkQ ∘ₗ u ∘ₗ (LinearMap.ker t).subtype

  have hq : Module.finrank k (LinearMap.ker q) ≤ e := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k) (M := LinearMap.ker q)
      (n := e + 1) hlt
    have hmem : ∀ j, u ((f j : LinearMap.ker t) : V) ∈ LinearMap.range t := by
      intro j
      have hj : (LinearMap.range t).mkQ (u ((f j : LinearMap.ker t) : V)) = 0 :=
        LinearMap.mem_ker.mp (f j).2
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hj
      exact hj
    choose y hy using fun j => LinearMap.mem_range.mp (hmem j)
    have hli : LinearIndependent k (fun j => ((f j : LinearMap.ker t) : V)) :=
      (hf.map' _ (Submodule.ker_subtype _)).map' _ (Submodule.ker_subtype _)
    exact h (fun j => ((f j : LinearMap.ker t) : V)) y
      (fun j => ⟨LinearMap.mem_ker.mp (f j : LinearMap.ker t).2, hy j⟩) hli
  have h1 := LinearMap.finrank_range_add_finrank_ker t
  have h2 := LinearMap.finrank_range_add_finrank_ker q
  have h3 := Submodule.finrank_le (LinearMap.range q)
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.range t)
  omega

theorem rank_le_rank_map_algebraMap (k K : Type) [Field k] [Field K] [Algebra k K] (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) k) : Φ.rank ≤ (Φ.map (algebraMap k K)).rank := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k)
    (M := LinearMap.range Φ.mulVecLin) (n := Φ.rank) le_rfl
  have hv : LinearIndependent k (fun i => ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    hf.map' _ (Submodule.ker_subtype _)

  have hw : LinearIndependent K
      (fun i => algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hmem : ∀ i, algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k) ∈
      LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := by
    intro i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (f i).2
    refine ⟨algebraMap k K ∘ y, ?_⟩
    rw [← hy]
    funext j
    simp only [Matrix.mulVecLin_apply, Function.comp_apply]
    exact (RingHom.map_mulVec _ _ _ j).symm
  let g : Fin Φ.rank → LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := fun i => ⟨_, hmem i⟩
  have hg : LinearIndependent K g := LinearIndependent.of_comp (LinearMap.range _).subtype hw
  have hc := hg.fintype_card_le_finrank
  rw [Fintype.card_fin] at hc
  exact hc

theorem finrank_ker_map_le_of_first_order_kernel : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  intro k K _ _ _ a e Φ U _ _ _ t u h
  have h1 := finrank_le_of_first_order_kernel k (LinearMap.ker Φ.mulVecLin) U e t u h
  have h2 := rank_le_rank_map_algebraMap k K a Φ
  have hk := LinearMap.finrank_range_add_finrank_ker Φ.mulVecLin
  have hK := LinearMap.finrank_range_add_finrank_ker (Φ.map (algebraMap k K)).mulVecLin
  rw [Module.finrank_fin_fun] at hk hK
  unfold Matrix.rank at h2
  omega
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
section
namespace GlobalTheory

theorem finsupp_vanishing_on_equiv_compl_prod :
    ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  intro I S n
  classical
  refine ⟨{
    toFun := fun l => l.1.subtypeDomain (· ∉ S)
    invFun := fun l' => ⟨l'.embDomain (Function.Embedding.subtype _), by
      intro v hv
      apply Finsupp.embDomain_notin_range
      rintro ⟨i, rfl⟩
      exact i.2 hv⟩
    left_inv := by
      rintro ⟨l, hl⟩
      apply Subtype.ext
      refine Finsupp.ext fun v => ?_
      by_cases hv : v ∈ S
      · show Finsupp.embDomain _ _ v = l v
        rw [Finsupp.embDomain_notin_range, hl v hv]
        rintro ⟨i, rfl⟩
        exact i.2 hv
      · show Finsupp.embDomain _ _ v = l v
        have := Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S))
          (l.subtypeDomain (· ∉ S)) ⟨v, hv⟩
        simpa using this
    right_inv := by
      intro l'
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.subtypeDomain_apply]
      exact Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S)) l' i }, ?_⟩
  intro M _ r _ l
  obtain ⟨l, hl⟩ := l
  show (l.subtypeDomain (· ∉ S)).prod (fun i v => r i.1 v) = l.prod r
  apply Finsupp.prod_subtypeDomain_index
  intro x hx hxS
  exact (Finsupp.mem_support_iff.mp hx) (hl x hxS)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardAddMonoidHomZmodLe
section
namespace GlobalTheory

theorem natCard_addMonoidHom_zmod_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod N) ≤ Nat.card A := by
  classical
  have : Fintype A := Fintype.ofFinite A

  have hinj : Function.Injective fun f : A →+ ZMod N ↦ (ZMod.stdAddChar (N := N)).compAddMonoidHom f :=
    AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar
  calc Nat.card (A →+ ZMod N) ≤ Nat.card (AddChar A ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card A := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

end GlobalTheory
end

