module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Mathlib.RingTheory.Nilpotent.Exp
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftUnramifiedUnipotentCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc

private theorem ul_exp_onto {A : Type} [CommRing A] [Algebra ℚ A] {n : A} (hn : IsNilpotent n) :
    ∃ x, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n :=
  _root_.UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto hn

private theorem t2Space_finite_padic_module {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module.Finite ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] : T2Space V := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  let e0 := (Module.finBasis ℚ_[l] V).equivFun
  exact T2Space.of_injective_continuous e0.injective
    (IsModuleTopology.continuous_of_linearMap e0.toLinearMap)

theorem UpperTheory.lift_unramified_unipotent_character :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] (p : B →ₐ[ℚ_[l]] B'), Function.Surjective p → (∀ a, p a = 0 → IsNilpotent a) → ∀ u' : GQ v →* B'ˣ, QCont l (fun g => (u' g : B')) → (∀ g ∈ Iq v, u' g = 1) → (∀ g, IsNilpotent ((u' g : B') - 1)) → ∃ u : GQ v →* Bˣ, QCont l (fun g => (u g : B)) ∧ (∀ g ∈ Iq v, u g = 1) ∧ ∀ g, p (u g : B) = (u' g : B') := by
  intro v l _ _ B B' _ _ _ _ _ _ p hp hker u' hc' hI' hn'
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : IsTopologicalAddGroup B' := IsModuleTopology.topologicalAddGroup ℚ_[l] B'
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B' := IsModuleTopology.toContinuousSMul ℚ_[l] B'
  haveI : T2Space B' := t2Space_finite_padic_module (l := l)
  obtain ⟨σ, hσ⟩ := (iqBasic v).2.2.2.1
  obtain ⟨x', hx', he'⟩ := ul_exp_onto (hn' σ)
  obtain ⟨x, rfl⟩ := hp x'
  have hx : IsNilpotent x := by
    obtain ⟨k, hk⟩ := hx'
    exact (hker (x ^ k) (by rw [map_pow, hk])).of_pow
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ v) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  let f : GQ v →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ v → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq v, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_⟩
  let f1 : GQ v →* B' := (p : B →* B').comp f
  let f2 : GQ v →* B' := (Units.coeHom B').comp u'
  have hcl : IsClosed ((f1.eqLocus f2 : Subgroup (GQ v)) : Set (GQ v)) :=
    isClosed_eq ((IsModuleTopology.continuous_of_linearMap p.toLinearMap).comp hf) hc'
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ f1.eqLocus f2 := by
    refine sup_le (fun k hk => ?_) ((Subgroup.zpowers_le).2 ?_)
    · change p (f k) = (u' k : B')
      rw [hfI k hk, hI' k hk, map_one, Units.val_one]
    · change p (IsNilpotent.exp (c σ • x)) = (u' σ : B')
      rw [hcσ, one_smul, IsNilpotent.map_exp hx, he', add_sub_cancel]
  have := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [frobDense σ hσ] at this
  exact this (Subgroup.mem_top g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusEigenvectorMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Bcr l) (δ : ℚ_[l]), c ≠ 0 → (PP l).φB c = algebraMap ℚ_[l] (Bcr l) δ * c → (PP l).ιB c ∈ ((PP l).PD (botExt l)).Fil 0 → ‖δ‖ ≤ 1 := by
  intro l _ c δ hc hφ hF
  by_contra hδ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ
  have hv : δ.valuation < 0 := by
    by_contra h
    exact hδ ((Padic.norm_le_one_iff_val_nonneg δ).2 (not_lt.1 h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ((a + 1 : ℕ) : ℤ) = -δ.valuation := ⟨(-δ.valuation - 1).toNat, by push_cast; omega⟩
  have hl : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ‖δ * (l : ℚ_[l]) ^ (a + 1)‖ = 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hδ0, ← zpow_add₀ hl, ha]
    simp
  let u : ℤ_[l] := ⟨δ * (l : ℚ_[l]) ^ (a + 1), hu.le⟩
  have huu : IsUnit u := PadicInt.isUnit_iff.2 hu
  obtain ⟨N, N', hNN, hN, hN', hφN, -⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace (l := l) (n := 1) (Matrix.of fun _ _ => u)
    (by rw [Matrix.det_fin_one]; exact huu)
  set P := PP l with hP
  set D := P.PD (botExt l) with hD
  have h1 : N 0 0 * N' 0 0 = 1 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply] using this
  have h2 : P.φB (N 0 0) = algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * N 0 0 := by
    have := congrFun (congrFun hφN 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at this
    exact this
  set w := N 0 0
  set w' := N' 0 0 with hw'
  have h3 : algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w' = w' := by
    have h := congrArg P.φB h1
    rw [map_mul, map_one, h2] at h
    linear_combination w' * h - (algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w') * h1
  have ht : P.φB D.t = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * D.t := by
    have := D.t_φ
    rw [P.PD_φ, P.PD_p, Algebra.smul_def] at this
    exact this
  have hb : D.φ (c * D.t ^ (a + 1) * w') = c * D.t ^ (a + 1) * w' := by
    rw [P.PD_φ, map_mul, map_mul, map_pow, hφ, ht, mul_pow]
    rw [map_mul, map_pow] at h3
    linear_combination (c * D.t ^ (a + 1)) * h3
  have ht0 : D.ι D.t ∈ D.Fil 0 := D.Fil_anti 0 D.mem_filtration_one
  have htp : ∀ n : ℕ, D.ι (D.t ^ n) ∈ D.Fil 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one]; exact D.one_mem
    | succ n ih => rw [pow_succ, map_mul]; exact D.Fil_mul 0 0 _ _ ih ht0
  have hF1 : D.ι (c * D.t ^ (a + 1) * w') ∈ D.Fil 1 := by
    rw [map_mul, map_mul, pow_succ, map_mul]
    have e1 : D.ι c ∈ D.Fil 0 := by rw [P.PD_ι]; exact hF
    have e2 : D.ι w' ∈ D.Fil 0 := by rw [P.PD_ι]; exact hN' 0 0
    exact D.Fil_mul 1 0 _ _ (D.Fil_mul 0 1 _ _ e1 (D.Fil_mul 0 1 _ _ (htp a) D.mem_filtration_one)) e2
  obtain ⟨r, hr⟩ := D.fund _ hb (D.Fil_anti 0 hF1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    have hw : IsUnit w' := IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)
    rw [eq_comm, hw.mul_left_eq_zero, (D.t_unit.pow _).mul_left_eq_zero] at hr
    exact hc hr
  have hone : (1 : P.R.BdR) ∈ D.Fil 1 := by
    rw [← hr, P.PD_ι, AlgHom.commutes] at hF1
    have := (D.Fil 1).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 r⁻¹) hF1
    rwa [algebraMap_smul, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one] at this
  have := D.Fil_mul 1 1 _ _ D.mem_filtration_one hone
  rw [mul_one] at this
  exact D.not_mem_filtration_two this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosBasic
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {E : Type} [Field E] [Algebra ℚ_[l] E]
  {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]

private noncomputable def spanT (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E]
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    (W : Submodule E V) : Submodule E (V ⊗[ℚ_[l]] Bdr l) :=
  Submodule.span E {y | ∃ v ∈ W, ∃ b ∈ ((PP l).PD (botExt l)).Fil 0, y = v ⊗ₜ[ℚ_[l]] b}

private theorem filT_le_spanT : FilT (l := l) E V 0 ≤ spanT l (⊤ : Submodule E V) := by
  rintro _ ⟨z, rfl⟩
  induction z with
  | tmul v b => exact Submodule.subset_span ⟨v, trivial, b.1, b.2, by simp⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

private theorem spanT_le_filT (W : Submodule E V) : spanT l W ≤ FilT (l := l) E V 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, -, b, hb, rfl⟩
  exact ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

private theorem spanT_bot : spanT l (⊥ : Submodule E V) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨v, hv, b, -, rfl⟩
  rw [Submodule.mem_bot] at hv
  simp [hv]

private theorem map_spanT {V' : Type} [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] E V'] (f : V →ₗ[E] V') (W : Submodule E V) (W' : Submodule E V')
    (hf : ∀ v ∈ W, f v ∈ W') (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W) :
    AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) y ∈ spanT l W' := by
  have : spanT l W ≤ (spanT l W').comap
      (AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, b, hb, rfl⟩
    exact Submodule.subset_span ⟨f v, hf v hv, b, hb, by simp⟩
  exact this hy

private theorem step (φ : G →* GQ l) (ρ : Representation E G V) (κ : G →* Eˣ)
    (hκ : FilD φ (chRep κ) 0 = ⊥) (W W' : Submodule E V) (x : V) (lam : V →ₗ[E] E)
    (hp : ∀ v ∈ W', v - lam v • x ∈ W)
    (heq : ∀ g, ∀ v ∈ W', lam (ρ g v) = (κ g : E) * lam v)
    (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W') (hD : y ∈ Ddr φ ρ) : y ∈ spanT l W := by
  set L := AlgebraTensorModule.map lam (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) with hL
  have hcomm : ∀ g, ∀ z ∈ spanT l W', L (actD φ ρ g z) = actD φ (chRep κ) g (L z) := by
    intro g z hz
    have : spanT l W' ≤ LinearMap.eqLocus (L ∘ₗ actD φ ρ g) (actD φ (chRep κ) g ∘ₗ L) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, b, hb, rfl⟩
      simp [LinearMap.mem_eqLocus, hL, actD, chRep, heq g v hv]
    exact this hz
  have h0 : L y = 0 := by
    have : L y ∈ FilD φ (chRep κ) 0 := by
      refine ⟨?_, spanT_le_filT ⊤ (map_spanT lam W' ⊤ (fun _ _ => trivial) y hy)⟩
      simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hD ⊢
      intro g
      rw [← hcomm g y hy, hD g]
    rwa [hκ, Submodule.mem_bot] at this
  have h1 := map_spanT (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam) W' W
    (fun v hv => by simpa using hp v hv) y hy
  have h2 : ∀ z : V ⊗[ℚ_[l]] Bdr l,
      AlgebraTensorModule.map (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) z =
      z - AlgebraTensorModule.map (LinearMap.toSpanSingleton E V x)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) (L z) := by
    intro z
    induction z with
    | tmul v b => simp [hL, sub_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
  rwa [h2, h0, map_zero, sub_zero] at h1

private theorem H0_eq_bot_of_filD_zero_eq_bot (φ : G →* GQ l) (ρ : Representation E G V) [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    (h : FilD φ ρ 0 = ⊥) : H0 ρ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_riemannRochSpace_iff_regularAt_everywhere] at hv
  haveI : Nontrivial (Bdr l) := nontrivial_of_ne 1 0 fun h1 =>
    ((PP l).PD (botExt l)).not_mem_filtration_two (by
      have : (((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t : Bdr l) = 0 := by
        rw [← mul_one (((PP l).PD (botExt l)).ι _), h1, mul_zero]
      rw [this]; exact zero_mem _)
  have hm : v ⊗ₜ[ℚ_[l]] (1 : Bdr l) ∈ FilD φ ρ 0 := by
    refine ⟨?_, v ⊗ₜ ⟨1, ((PP l).PD (botExt l)).one_mem⟩, by simp⟩
    simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    simp [actD, hv g]
  rw [h, Submodule.mem_bot] at hm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ_[l] (one_ne_zero : (1 : Bdr l) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid ℚ_[l] V (TensorProduct.map LinearMap.id f z)) hm
  simpa [hf] using this

end SlopeTestRemainingChoices

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.posBasic :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0 ρ = ⊥ ∧ FilD φ ρ 0 = ⊥ ∧ Module.Finite E ↥(finiteCohomology φ ρ) ∧ finrank E ↥(finiteCohomology φ ρ) = φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  obtain ⟨hdr, n, F, hF0, hFn, hF⟩ := hpos
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have key : ∀ i ≤ n, (∀ g, ∀ v ∈ F i, ρ g v ∈ F i) ∧ ∀ y ∈ spanT l (F i), y ∈ Ddr φ ρ → y = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hF0, spanT_bot]
      refine ⟨fun g v hv => ?_, fun y hy _ => hy⟩
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i ih =>
      intro hi
      obtain ⟨hst, hz⟩ := ih (by omega)
      obtain ⟨hle, κ, ⟨w, hw, hκ⟩, x, hsup, hx⟩ := hF i (by omega)
      by_cases hxi : x ∈ F i
      · have : F (i + 1) = F i := by
          rw [hsup, sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hxi
        rw [this]; exact ⟨hst, hz⟩
      obtain ⟨lam, hl1, hl0⟩ : ∃ lam : V →ₗ[E] E, lam x = 1 ∧ ∀ v ∈ F i, lam v = 0 := by
        have hne : (F i).mkQ x ≠ 0 := by simpa using hxi
        obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one E hne
        refine ⟨f ∘ₗ (F i).mkQ, hf, fun v hv => ?_⟩
        have : (F i).mkQ v = 0 := by simpa using hv
        rw [LinearMap.comp_apply, this, map_zero]
      have hdec : ∀ v ∈ F (i + 1), ∃ u ∈ F i, ∃ c : E, v = u + c • x := by
        intro v hv
        rw [hsup, Submodule.mem_sup] at hv
        obtain ⟨u, hu, z, hz, rfl⟩ := hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        exact ⟨u, hu, c, rfl⟩
      have hx1 : x ∈ F (i + 1) := by
        rw [hsup]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
      have hlx : ∀ g, lam (ρ g x) = (κ g : E) := by
        intro g
        have := hl0 _ (hx g)
        rwa [map_sub, map_smul, hl1, smul_eq_mul, mul_one, sub_eq_zero] at this
      have hcont : Continuous (fun g => (κ g : E)) := by
        have h1 : Continuous (lam.restrictScalars ℚ_[l]) :=
          IsModuleTopology.continuous_of_linearMap _
        have h2 : Continuous (fun g => ρ g x) := hρ.comp (Continuous.prodMk_left x)
        have := h1.comp h2
        convert this using 1
        funext g
        exact (hlx g).symm
      have hfil := ((charFil φ hφ κ hcont w hκ).2 0).2 (by omega)
      refine ⟨fun g v hv => ?_, fun y hy hD => hz y (step φ ρ κ hfil (F i) (F (i + 1)) x lam ?_ ?_ y hy hD) hD⟩
      · obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        rw [map_add (f := _), map_smul]
        refine add_mem (hle (hst g u hu)) (Submodule.smul_mem _ _ ?_)
        have := add_mem (hle (hx g)) (Submodule.smul_mem _ (κ g : E) hx1)
        rwa [sub_add_cancel] at this
      · intro v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simpa [hl0 u hu, hl1] using hu
      · intro g v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simp [hl0 u hu, hl1, hl0 _ (hst g u hu), hlx, mul_comm]
  have hfil : FilD φ ρ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact (key n le_rfl).2 y (hFn ▸ filT_le_spanT hy.2) hy.1
  have hH0 := H0_eq_bot_of_filD_zero_eq_bot φ ρ hfil
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ ρ hρ hdr
  refine ⟨hH0, hfil, hfin, ?_⟩
  rw [hfil, hH0] at hdim
  simpa using hdim
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem grows_le {l : ℕ} (hl : 1 < l) {a : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l a t) :
    s ≤ t := by
  obtain ⟨_, h⟩ := h
  obtain ⟨C, h'⟩ := h'
  have := (Nat.pow_le_pow_iff_right hl).1 ((h (C + 1) C.succ_pos).1.trans (h' (C + 1) C.succ_pos).2)
  by_contra hc
  have : (C + 1) * (t + 1) ≤ (C + 1) * s := Nat.mul_le_mul_left _ (by omega)
  nlinarith

private theorem grows_unique {l : ℕ} (hl : 1 < l) {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t)
    (e : ∀ m, a m = b m) : s = t := by
  obtain rfl : a = b := funext e
  exact le_antisymm (grows_le hl h h') (grows_le hl h' h)

private theorem grows_mul {l : ℕ} {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t) :
    Grows l (fun m => a m * b m) (s + t) := by
  obtain ⟨C, h⟩ := h
  obtain ⟨D, h'⟩ := h'
  refine ⟨C + D, fun m hm => ⟨?_, ?_⟩⟩
  · rw [mul_add, pow_add]
    exact Nat.mul_le_mul (h m hm).1 (h' m hm).1
  · rw [show m * (s + t) + (C + D) = (m * s + C) + (m * t + D) by ring, pow_add]
    exact Nat.mul_le_mul (h m hm).2 (h' m hm).2

private theorem grows_pow (l n d : ℕ) : Grows l (fun m => (l ^ (m * n)) ^ d) (d * n) :=
  ⟨0, fun m _ => by
    have : (l ^ (m * n)) ^ d = l ^ (m * (d * n)) := by rw [← pow_mul]; congr 1; ring
    simp [this]⟩

private theorem tate_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧
      finrank ℤ_[l] (H1 ρ) = finrank ℤ_[l] ↥(H0 ρ) + finrank ℤ_[l] (H2 ρ) + d * n ∧
      finrank ℤ_[l] (H2 ρ) = finrank ℤ_[l] ((Fin n → ℤ_[l]) ⧸ coSub χ ρ) := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hm := fun m => hF _ (redRep ρ m) (contAction_redRep h m)
  obtain ⟨f1, f2, g0, g1, g2⟩ := UpperTheory.lattice_cohomology_finite_and_growth_of_finGen ρ h (UpperTheory.latticeCochains_finGen_of_finLevel hF ρ h) fun m => ⟨(hm m).1, (hm m).2.1⟩
  refine ⟨f1, f2, grows_unique hl g1 (grows_mul (grows_mul g0 g2) (grows_pow l n d)) fun m => ?_,
    grows_unique hl g2 (UpperTheory.card_quotient_powSubmodule_grows_finrank l _) fun m => ?_⟩
  · rw [(hm m).2.2.2.1, card_quot_lSub]
  · rw [(hm m).2.2.2.2, UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants]

private theorem tate_Q {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    Module.Finite ℚ_[l] (H1 ρ) ∧ Module.Finite ℚ_[l] (H2 ρ) ∧
      finrank ℚ_[l] (H1 ρ) = finrank ℚ_[l] ↥(H0 ρ) + finrank ℚ_[l] (H2 ρ) + d * finrank ℚ_[l] V ∧
      finrank ℚ_[l] (H2 ρ) =
        finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) := by
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ρT, j, hT, hj, he, hs⟩ := UpperTheory.exists_invariant_lattice_openEmbedding ρ h
  obtain ⟨r0, r1, r2⟩ := UpperTheory.rank_cohomology_rational_eq_rank_lattice ρ h ρT j hT hj he hs
  obtain ⟨f1, f2, e1, e2⟩ := tate_lattice hF ρT hT
  have q0 : finrank ℚ_[l] ↥(H0 ρ) = finrank ℤ_[l] ↥(H0 ρT) := congrArg Cardinal.toNat r0
  have q1 : finrank ℚ_[l] (H1 ρ) = finrank ℤ_[l] (H1 ρT) := congrArg Cardinal.toNat r1
  have q2 : finrank ℚ_[l] (H2 ρ) = finrank ℤ_[l] (H2 ρT) := congrArg Cardinal.toNat r2
  refine ⟨Module.rank_lt_aleph0_iff.1 (r1 ▸ Module.rank_lt_aleph0 _ _),
    Module.rank_lt_aleph0_iff.1 (r2 ▸ Module.rank_lt_aleph0 _ _), ?_, ?_⟩
  · rw [q0, q1, q2, e1]
  · rw [q2, e2, UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants χ ρ ρT j hj.injective he hs]

private theorem finrank_H0dual {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (χ : G →* Eˣ) (ρ : Representation E G V) :
    finrank E ↥(H0dual χ ρ) = finrank E (V ⧸ coSub χ ρ) := by
  have : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
    ext f
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      refine (Submodule.span_le (p := LinearMap.ker f)).2 ?_ hw
      rintro _ ⟨g, x, rfl⟩
      simp [hf g x]
    · intro hf g x
      have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
      simpa [sub_eq_zero] using this
  rw [this, ← (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq, Subspace.dual_finrank_eq]

private theorem coSub_res {Q E G V : Type} [Field Q] [Field E] [Algebra Q E] [Group G] [AddCommGroup V]
    [Module E V] [Module Q V] [IsScalarTower Q E V] (χ : G →* Qˣ) (χ' : G →* Eˣ)
    (hχ : ∀ g, ((χ' g : Eˣ) : E) = algebraMap Q E (χ g : Qˣ)) (ρ : Representation E G V) :
    coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    exact Submodule.subset_span ⟨g, x, by rw [hχ, algebraMap_smul]; rfl⟩
  · intro y hy
    have key : ∀ c : E, c • y ∈ coSub χ (resCoef Q ρ) := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, x, rfl⟩ := hy
        intro c
        refine Submodule.subset_span ⟨g, c • x, ?_⟩
        change _ = ρ g (c • x) - _
        rw [hχ, algebraMap_smul, smul_sub, map_smul, smul_comm c (χ g : Q)]
      | zero => intro c; simp
      | add a b _ _ ha hb => intro c; rw [smul_add]; exact add_mem (ha c) (hb c)
      | smul a b _ hb => intro c; rw [smul_smul]; exact hb _
    simpa using key 1

theorem UpperTheory.V.Loc.tateRat :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Module.Finite E (H1 ρ) ∧ Module.Finite E (H2 ρ) ∧ finrank E (H1 ρ) = finrank E ↥(H0 ρ) + finrank E (H2 ρ) + (if v = l then φ.range.index * finrank E V else 0) ∧ finrank E (H2 ρ) = finrank E ↥(H0dual ((cycA v l E).comp φ) ρ) := by
  intro hP v l _ _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  haveI : CompactSpace G := by
    have hc : IsClosed (φ.range : Set (GQ v)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
    exact (⟨hφ.isEmbedding, hc⟩ : IsClosedEmbedding φ).compactSpace
  haveI : ContinuousConstSMul ℚ_[l] V := ⟨fun c => by
    simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap ℚ_[l] E c)⟩
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨f1, f2, e1, e2⟩ := tate_Q (UpperTheory.finite_level_of_finite_level_mod l G _ _ (UpperTheory.finiteLevel_cyclotomic_of_openEmbedding hP φ hφ)) (resCoef ℚ_[l] ρ) h
  obtain ⟨⟨a0⟩, ⟨a1⟩, ⟨a2⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℚ_[l] ρ
  haveI := Module.Finite.equiv a1
  haveI := Module.Finite.equiv a2
  have hd : 0 < finrank ℚ_[l] E := finrank_pos
  rw [coSub_res ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp ((cyc v l).comp φ))
      ((cycA v l E).comp φ)
      (fun g => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])) ρ,
    (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _).finrank_eq, a2.finrank_eq,
    ← finrank_mul_finrank ℚ_[l] E (H2 ρ), ← finrank_mul_finrank ℚ_[l] E (V ⧸ _)] at e2
  rw [a0.finrank_eq, a1.finrank_eq, a2.finrank_eq, ← finrank_mul_finrank ℚ_[l] E (H2 ρ),
    ← finrank_mul_finrank ℚ_[l] E (H1 ρ), ← finrank_mul_finrank ℚ_[l] E ↥(H0 ρ),
    ← finrank_mul_finrank ℚ_[l] E V] at e1
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, Module.Finite.of_restrictScalars_finite ℚ_[l] E _,
    Nat.eq_of_mul_eq_mul_left hd ?_, ?_⟩
  · rw [e1]
    split_ifs <;> ring
  · rw [finrank_H0dual]
    exact Nat.eq_of_mul_eq_mul_left hd e2
end

