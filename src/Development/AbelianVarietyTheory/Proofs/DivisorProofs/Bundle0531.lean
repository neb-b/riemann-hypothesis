module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear
section
noncomputable section

open Module
open scoped TensorProduct NumberField

namespace GlobalTheory.BadCount.RankRead

theorem finrank_iInf_ker_semilinear {L M W X ι κ : Type} [Field L] [Field M] [AddCommGroup W] [Module L W] [AddCommGroup X]
    [Module M X] [Finite ι] [Finite κ] {σ : L →+* M} (Φ : W →ₛₗ[σ] X) (b : Basis κ L W) (hb : LinearIndependent M fun k => Φ (b k))
    (a : ι → W →ₗ[L] W) (a' : ι → X →ₗ[M] X) (h : ∀ i w, a' i (Φ w) = Φ (a i w)) :
    finrank L (⨅ i, LinearMap.ker (a i) : Submodule L W) =
      finrank M ((⨅ i, LinearMap.ker (a' i)) ⊓ Submodule.span M (Set.range Φ) : Submodule M X) := by
  haveI := Module.Finite.of_basis b
  letI : Algebra L M := σ.toAlgebra
  letI : Module L X := Module.compHom X σ
  haveI : IsScalarTower L M X := ⟨fun x y z => mul_smul (σ x) y z⟩
  let U := Submodule.span M (Set.range Φ)
  let f : W →ₗ[L] U :=
    { toFun := fun w => ⟨Φ w, Submodule.subset_span ⟨w, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add Φ x y)
      map_smul' := fun x y => Subtype.ext (map_smulₛₗ Φ x y) }
  have hU : U = Submodule.span M (Set.range fun k => Φ (b k)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩))
    rintro _ ⟨w, rfl⟩
    haveI := Fintype.ofFinite κ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis κ M U := (Basis.span hb).map (LinearEquiv.ofEq _ _ hU.symm)
  have hc : ∀ k, c k = f (b k) := fun k => Subtype.ext (by simp [c, f])
  have hf : IsBaseChange M f := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)) fun m => ?_
    have : ((((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)).toLinearMap.restrictScalars L) ∘ₗ
        TensorProduct.mk L M W 1) = f := b.ext fun k => by
      rw [← hc]
      simp [← Algebra.TensorProduct.basis_apply]
    exact LinearMap.congr_fun this m
  have hm : ∀ i, ∀ x ∈ U, a' i x ∈ U := fun i => Submodule.span_le (p := U.comap (a' i)) |>.2 (by
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span ⟨_, (h i w).symm⟩)
  rw [← GlobalTheory.finrank_iInf_ker_of_isBaseChange L M W U ι f a (fun i => (a' i).restrict (hm i)) hf
    (fun i w => Subtype.ext (h i w)), ← Submodule.finrank_map_subtype_eq U]
  refine congrArg (fun N : Submodule M X => finrank M N) (Submodule.ext fun x => ?_)
  simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_inf]
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨fun i => congrArg Subtype.val (hy i), y.2⟩,
    fun ⟨h1, h2⟩ => ⟨⟨x, h2⟩, fun i => Subtype.ext (h1 i), rfl⟩⟩

def twistExt {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) : Representation M Γ (M ⊗[F] V) where
  toFun γ := ((χ γ : Mˣ) : M) • (τ γ).baseChange M
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' γ δ := by
    rw [map_mul, map_mul, LinearMap.baseChange_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistExt_tmul {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) (γ : Γ) (m : M) (v : V) :
    twistExt τ χ γ (m ⊗ₜ[F] v) = ((χ γ : Mˣ) : M) • (m ⊗ₜ[F] τ γ v) := rfl

theorem finrank_eq {K L F M C W V G G' Γ : Type} [Field K] [Field L] [Field F] [Field M] [Algebra K L] [Algebra F M]
    [AddCommGroup C] [Module K C] [AddCommGroup W] [Module L W] [Module K W] [IsScalarTower K L W] [AddCommGroup V] [Module F V]
    [Group G] [Fintype G] [Group G'] [Group Γ] [Finite Γ] {j : K →+* F} (σ : L →+* M)
    (hσ : ∀ a, σ (algebraMap K L a) = algebraMap F M (j a)) (ε : C →ₗ[K] W) (π : C →ₛₗ[j] V) {n : ℕ} (b : Fin n → C)
    (b₁ : Submodule.span K (Set.range b) = ⊤) (b₂ : LinearIndependent L fun k => ε (b k))
    (b₃ : Submodule.span L (Set.range fun k => ε (b k)) = ⊤) (b₄ : LinearIndependent F fun k => π (b k))
    (ρ : G →* (W →ₗ[L] W)) (chi : G →* Lˣ) (τ : Representation F Γ V) (θ : Γ →* G) (c : G ≃* G') (s : G' →* Γ)
    (hs : ∀ g, θ (s (c g)) = g) (hρ : ∀ γ f, ∃ f', ρ (θ γ) (ε f) = ε f' ∧ τ γ (π f) = π f')
    (hinv : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (P : Subgroup G) (lam : P →* Lˣ) (Q : Subgroup Γ) (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ P) (lamb : Q →* Mˣ)
    (hlam : ∀ γ : Q, ((lamb γ : Mˣ) : M) = σ (lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ))
    (S : Submodule L W) (hS : ∀ w, w ∈ S ↔ ∀ p : P, ρ p w = ((chi p * lam p : Lˣ) : L) • w)
    (eC : G → L) (e : MonoidAlgebra M G') (he : ∀ g, σ (eC g) = e.coeff (c g)) :
    finrank L S = finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb) ∧
    finrank L (S ⊓ LinearMap.ker (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) : Submodule L W) =
      finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom ((twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹).comp s :
          Representation M G' (M ⊗[F] V)) e) : Submodule M (M ⊗[F] V)) := by
  set R := twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹ with hR
  let bW : Basis (Fin n) L W := Basis.mk b₂ b₃.ge
  let Φ : W →ₛₗ[σ] M ⊗[F] V :=
    { toFun := fun w => ∑ k, σ (bW.repr w k) • ((1 : M) ⊗ₜ[F] π (b k))
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun x y => by simp [Finset.smul_sum, mul_smul] }
  have hΦb : ∀ k, Φ (bW k) = (1 : M) ⊗ₜ[F] π (b k) := fun k => by
    show ∑ l, σ (bW.repr (bW k) l) • _ = _
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Finsupp.single_eq_of_ne hl]) (by simp)]
    simp
  have hΦ : ∀ f, Φ (ε f) = (1 : M) ⊗ₜ[F] π f := fun f => by
    have hf : f ∈ Submodule.span K (Set.range b) := b₁ ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; rw [← hΦb, Basis.mk_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), TensorProduct.tmul_add]
    | smul t x _ hx =>
      rw [map_smul, ← algebraMap_smul L, map_smulₛₗ, hx, map_smulₛₗ, hσ, algebraMap_smul, TensorProduct.tmul_smul]
  have hind : LinearIndependent M fun k => Φ (bW k) := by
    simp only [hΦb]
    exact Module.Flat.linearIndependent_one_tmul b₄
  have hRΦ : ∀ γ w, R γ (Φ w) = Φ ((((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) w) := fun γ w => by
    rw [← bW.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨f', h1, h2⟩ := hρ γ (b k)
    rw [hΦb, Basis.mk_apply, h1, hΦ, hR, twistExt_tmul, h2, smul_comm]
    simp
  have hE : eig R Q lamb ≤ Submodule.span M (Set.range Φ) := fun x hx => by
    have h0 := GlobalTheory.GaloisDescent.span_image_iInf (TensorProduct.isBaseChange F V M)
      fun γ : θ.ker => LinearMap.ker (τ γ - LinearMap.id)
    have h1 : x ∈ Submodule.span M (TensorProduct.mk F M V 1 ''
        (⨅ γ : θ.ker, LinearMap.ker (τ γ - LinearMap.id) : Submodule F V)) := by
      rw [h0, Submodule.mem_iInf]
      intro γ
      have hγ : θ γ = 1 := γ.2
      have hq : (γ : Γ) ∈ Q := (hQ _).2 (hγ ▸ P.one_mem)
      rw [GlobalTheory.GaloisDescent.span_image_ker (TensorProduct.isBaseChange F V M) (TensorProduct.isBaseChange F V M) _
        ((τ γ).baseChange M - LinearMap.id) (fun v => by simp [TensorProduct.tmul_sub])]
      have := (mem_eig R Q lamb x).1 hx ⟨γ, hq⟩
      rw [hlam, show (⟨θ γ, (hQ _).1 hq⟩ : P) = 1 from Subtype.ext hγ] at this
      simpa [hR, twistExt, hγ, sub_eq_zero] using this
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨v, hv, rfl⟩
    have hv' := hinv v fun γ hγ => sub_eq_zero.1 ((Submodule.mem_iInf _).1 hv ⟨γ, hγ⟩)
    clear hv
    induction hv' using Submodule.span_induction with
    | mem _ h => obtain ⟨f, rfl⟩ := h; exact Submodule.subset_span ⟨_, hΦ f⟩
    | zero => simp
    | add x y _ _ hx hy =>
      change (TensorProduct.mk F M V 1) (x + y) ∈ Submodule.span M (Set.range Φ)
      rw [map_add]
      exact add_mem hx hy
    | smul t x _ hx => rw [map_smul, ← algebraMap_smul M]; exact Submodule.smul_mem _ _ hx
  let a : Q → W →ₗ[L] W := fun γ => (((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) - ((lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ) : L) • LinearMap.id
  let a' : Q → M ⊗[F] V →ₗ[M] M ⊗[F] V := fun γ => R γ - ((lamb γ : Mˣ) : M) • LinearMap.id
  have ha : ∀ γ w, a' γ (Φ w) = Φ (a γ w) := fun γ w => by
    simp only [a, a', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hRΦ, map_sub, map_smulₛₗ, hlam]
  have hSa : S = ⨅ γ, LinearMap.ker (a γ) := by
    ext w
    have key : ∀ (g : G) (x : Lˣ), (((chi g)⁻¹ : Lˣ) : L) • ρ g w - (x : L) • w = 0 ↔ ρ g w = ((chi g * x : Lˣ) : L) • w :=
      fun g x => by rw [sub_eq_zero, ← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul, Units.val_mul]
    rw [hS, Submodule.mem_iInf]
    refine ⟨fun h γ => (key _ _).2 (h ⟨θ γ, (hQ _).1 γ.2⟩), fun h p => ?_⟩
    have := (key _ _).1 (h ⟨s (c p), (hQ _).2 (by rw [hs]; exact p.2)⟩)
    simpa only [hs] using this
  have hEa : eig R Q lamb = ⨅ γ, LinearMap.ker (a' γ) := rfl
  refine ⟨by rw [hSa, finrank_iInf_ker_semilinear Φ bW hind a a' ha, ← hEa, inf_eq_left.2 hE], ?_⟩
  have h2 := finrank_iInf_ker_semilinear Φ bW hind (fun o : Option Q => o.elim (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) a)
    (fun o => o.elim (Representation.asAlgebraHom (R.comp s : Representation M G' (M ⊗[F] V)) e) a') (by
      rintro (_ | γ) w
      · haveI := Fintype.ofEquiv G c.toEquiv
        simp only [Option.elim]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
          LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        refine (Fintype.sum_equiv c.toEquiv _ _ fun g => ?_).symm
        rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul, map_smulₛₗ, he]
        exact congrArg _ (by rw [MonoidHom.comp_apply, hRΦ]; simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hs])
      · exact ha γ w)
  rw [iInf_option, iInf_option] at h2
  simp only [Option.elim] at h2
  rw [hSa, inf_comm]
  refine h2.trans (congrArg (fun N : Submodule M (M ⊗[F] V) => finrank M N) ?_)
  rw [← hEa, inf_assoc, inf_eq_left.2 hE, inf_comm]

theorem rkK_inf {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL]
    [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL]
    [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (hK : A.IsKsForm) (hM : A.MKFull) (S : Submodule LL WL) :
    Formalism.HN.rkK (Submodule.span (𝓞 LL) (A.MK : Set WL) ⊓ S.restrictScalars (𝓞 LL)) = finrank LL S := by
  obtain ⟨n, b, h1, -, -, -, h5⟩ := hK
  have h : S ≤ Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) := by
    refine le_top.trans (h5.ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨k, rfl⟩
    exact Submodule.span_mono Submodule.subset_span (Submodule.span_le_restrictScalars Ks LL _ (hM.2 ▸ h1 k))
  rw [Formalism.HN.rkK, GlobalTheory.span_inf_restrictScalars_eq LL h]

end GlobalTheory.BadCount.RankRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinearStandardBasis
section
open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_semilinear : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V]
    [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V),
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ →
    ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V),
      (∀ i v, a' i (f v) = f (a i v)) →
      finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) =
        finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  intro K V ι _ _ _ _ σ N f hli hsp a a' ha
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Module K V := Module.compHom V σ
  haveI : IsScalarTower K ℂ V := ⟨fun k c v => by
    show (σ k * c) • v = σ k • c • v
    rw [mul_smul]⟩
  let g : (Fin N → K) →ₗ[K] V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }
  have hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [f.map_smulₛₗ, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis (Fin N) ℂ V := Basis.mk hli hsp'.ge
  have hc : ∀ k, c k = f (Pi.single k 1) := fun k => Basis.mk_apply _ _ _
  let e := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)
  have hbc : IsBaseChange ℂ g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g := by
      refine (Pi.basisFun K (Fin N)).ext fun k => ?_
      have := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hc, Pi.basisFun_apply]
      rfl
    exact congrArg (fun φ => φ m) h
  exact (finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegular
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_idem_le_of_embReg : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V]
    [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ,
    (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧
      finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  intro K Γ V _ _ _ _ _ _ ρ H n hE a ha hidem
  obtain ⟨j, hj, hjρ⟩ := hE
  classical
  let ψ := MonoidAlgebra.mapDomainAlgHom K K H.subtype
  have hψinj : Function.Injective ψ := MonoidAlgebra.mapDomain_injective Subtype.val_injective
  let a' : MonoidAlgebra K H :=
    MonoidAlgebra.ofCoeff (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn)
  have hψa : ψ a' = a := by
    apply MonoidAlgebra.coeff_injective
    show Finsupp.mapDomain Subtype.val (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn) = a.coeff
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro g hg
    exact ⟨⟨g, ha g (by simpa using hg)⟩, rfl⟩
  have hidem' : a' * a' = a' := hψinj (by rw [map_mul, hψa, hidem])
  have hc1 : a'.coeff 1 = a.coeff 1 := rfl
  have key : ∀ (b : MonoidAlgebra K H) (v : V) (i : Fin n), j (ρ.asAlgebraHom (ψ b) v) i = b * j v i := by
    intro b
    induction b using MonoidAlgebra.induction_on with
    | of h =>
      intro v i
      have : ψ (MonoidAlgebra.of K H h) = MonoidAlgebra.of K Γ (h : Γ) := by
        simp [ψ]
      rw [this, Representation.asAlgebraHom_of, hjρ h v i]
      rfl
    | add b c hb hc => intro v i; simp [map_add (f := _), LinearMap.add_apply, hb, hc, add_mul]
    | smul r b hb => intro v i; simp [map_smul, LinearMap.smul_apply, hb, smul_mul_assoc]
  refine ⟨finrank K (LinearMap.range (LinearMap.mulLeft K a')), ?_, ?_⟩
  · rw [_root_.GlobalTheory.BadCount.finrank_range_mulLeft_idem K H a' hidem', hc1]
  · let R := LinearMap.range (LinearMap.mulLeft K a')
    let g : LinearMap.range (ρ.asAlgebraHom a) →ₗ[K] (Fin n → R) :=
      LinearMap.pi fun i => LinearMap.codRestrict R
        ((LinearMap.proj i).comp (j.comp (LinearMap.range (ρ.asAlgebraHom a)).subtype)) (by
          rintro ⟨x, v, rfl⟩
          refine ⟨j v i, ?_⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply]
          rw [← hψa, key])
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.val_injective
      apply hj
      funext i
      have := congrArg (fun f => ((f i : R) : MonoidAlgebra K H)) hxy
      simpa [g] using this
    have := LinearMap.finrank_le_finrank_of_injective hg
    rw [Module.finrank_pi_fintype] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargementStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fittingDatum_baseChange_localEnlargement : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
    Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
    ∃ (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A₁) EA') (_ : Algebra A₁ EA')
      (_ : IsScalarTower A₁ (Polynomial A₁) EA') (_ : Algebra.Etale (Polynomial A₁) EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA' QA' jA' ψA' DA' actA' ∧
      (∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))
        (h : DA →+* DA'), ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA').comp β) ∧
      ∃ γ : EA →+* EA',
        γ.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial A₁) EA').comp (Polynomial.mapRingHom f) ∧
        jA'.comp ((algebraMap EA' (Localization.AtPrime QA')).comp γ) = jA.comp (algebraMap EA (Localization.AtPrime QA)) ∧
        QA' = (maximalIdeal O).comap (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) ∧
        (∀ (Z : Type) [CommRing Z] (u : Polynomial A₁ →+* Z) (v : EA →+* Z),
          u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap (Polynomial A) EA) →
          ∃ w : EA' →+* Z, w.comp (algebraMap (Polynomial A₁) EA') = u ∧ w.comp γ = v) ∧
        (∀ (Z : Type) [CommRing Z] (w₁ w₂ : EA' →+* Z),
          w₁.comp (algebraMap (Polynomial A₁) EA') = w₂.comp (algebraMap (Polynomial A₁) EA') →
          w₁.comp γ = w₂.comp γ → w₁ = w₂) := by
  first | (exact @GlobalTheory.EnlargeBaseChange.fits_baseChange) | (exact GlobalTheory.EnlargeBaseChange.fits_baseChange) | (intros; apply GlobalTheory.EnlargeBaseChange.fits_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderivStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_norm_bounds_mul_X_pderiv : ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι → ∀ (i : σ) (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d → ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧ ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  first | exact @GlobalTheory.FockNormBound.fock_norm_bounds | exact GlobalTheory.FockNormBound.fock_norm_bounds | (intros; apply GlobalTheory.FockNormBound.fock_norm_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdeal
section
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.FrameCong

theorem coord_mem_idS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (I : Ideal (𝓞 E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) :
    ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F) := by
  refine Submodule.span_induction (p := fun w _ => ∀ i, ∃ s ∈ idS F I,
    (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on (p := fun m => ∀ i, ∃ s ∈ idS F I,
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m k))) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) hm ?_ ?_
    · intro a ha u hu i
      have hu' : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨u, hu, rfl⟩
      have t := (hβ _).1 hu' i
      refine ⟨oToS F E a * ⟨_, t⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
      have e : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k)) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) := by
        funext k
        show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    · intro m1 m2 h1 h2 i
      obtain ⟨s1, hs1, e1⟩ := h1 i
      obtain ⟨s2, hs2, e2⟩ := h2 i
      refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
      have : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((m1 + m2) k)) =
          (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m1 k)) +
            (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m2 k)) := by
        funext k; simp [map_add (f := _)]
      rw [this, Matrix.mulVec_add, Pi.add_apply, e1, e2]
      rfl
  · intro i
    exact ⟨0, zero_mem _, by simp⟩
  · intro a b _ _ ha hb i
    obtain ⟨s1, hs1, e1⟩ := ha i
    obtain ⟨s2, hs2, e2⟩ := hb i
    refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply, e1, e2]
    rfl
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [show c • a = (c : E ⊗[F] Formalism.L2.Herm.Af F) • a from rfl, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, e]
    rfl

theorem redFn_eq_one_of_congr : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ →
    x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) →
    ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  intro F E _ _ _ _ _ n β x Λ hβ hx I hcong PP hPP
  classical
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_frGL]
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  apply Units.ext
  ext i j
  have hv : β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    refine (hβ _).2 fun k => ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  obtain ⟨s, hs, es⟩ := coord_mem_idS β Λ hβ I _ (hcong _ hv) i
  have hcomp : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) -
        β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) = (Y - 1) *ᵥ Pi.single j 1 := by
    have hm1 : (β⁻¹).1 * (β.1 * Y * (β⁻¹).1) * β.1 = Y := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm1, Units.inv_mul,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hcomp, Matrix.mulVec_single_one, Matrix.col_apply] at es
  have e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hs' : (y.1 - 1) i j = s := Subtype.ext (e5.trans es)
  have hmem : (y.1 - 1) i j ∈ idS F PP.asIdeal := hs' ▸ Ideal.map_mono hPP hs
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.FrameCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartIffConvolutionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y → (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  first | (exact @GlobalTheory.Shin.kills_iff_conv) | (exact GlobalTheory.Shin.kills_iff_conv) | (intros; apply GlobalTheory.Shin.kills_iff_conv <;> assumption)
end

