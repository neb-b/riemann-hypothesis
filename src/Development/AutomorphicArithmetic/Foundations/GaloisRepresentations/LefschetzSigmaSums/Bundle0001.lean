module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCoeffOcc
section
set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem coeffOcc_of : CoeffOcc := by
  intro d n t c h hinj hc hEq i
  set P : ℂ[X] := ∑ a ∈ Finset.range (d + 1), C ((-1) ^ a * t a) * X ^ a with hPdef
  set Q : ℂ[X] := ∑ j, C c * X ^ (h j) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro y
    simp only [hPdef, hQdef, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← Finset.mul_sum, ← hEq y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [neg_pow]
    ring
  have hQ : Q.coeff (h i) = c := by
    simp only [hQdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun e => hji (hinj e).symm), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hP : P.coeff (h i) = if h i ∈ Finset.range (d + 1) then (-1) ^ (h i) * t (h i) else 0 := by
    simp only [hPdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  intro ht
  rw [hPQ, hQ] at hP
  split_ifs at hP with hlt
  · rw [ht, mul_zero] at hP
    exact hc hP
  · exact hc hP

end UpperTheory.Gal.LocalSmoothExtension
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PConjRep
section
set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension

private def Tw (_σ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance twAdd (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : AddCommGroup (Tw σ V) :=
  inferInstanceAs (AddCommGroup V)

private instance twMod (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Tw σ V) :=
  Module.compHom V (σ.symm : ℂ →+* ℂ)

private def toTw (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Tw σ V := AddEquiv.refl V

private theorem tw_smul (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : V) :
    toTw σ V (c • x) = σ c • toTw σ V x := by
  change c • x = ((σ.symm : ℂ →+* ℂ) (σ c)) • x
  simp

private theorem tw_smul' (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : Tw σ V) :
    c • x = toTw σ V (σ.symm c • (toTw σ V).symm x) := rfl

private theorem tw_finite (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] : FiniteDimensional ℂ (Tw σ V) := by
  let b := Module.finBasis ℂ V
  have hsm : ∀ (c : ℂ) (y : Tw σ V), (toTw σ V).symm (c • y) = σ.symm c • (toTw σ V).symm y :=
    fun c y => rfl
  let b' : Module.Basis (Fin (Module.finrank ℂ V)) ℂ (Tw σ V) := Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))
      invFun := fun f => toTw σ V (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        simp [hsm]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))) =
              b.repr ((toTw σ V).symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }
  exact Module.Finite.of_basis b'

private def twMap (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] V) :
    Tw σ V →ₗ[ℂ] Tw σ V where
  toFun x := toTw σ V (T ((toTw σ V).symm x))
  map_add' x y := by simp
  map_smul' c x := by
    rw [RingHom.id_apply, tw_smul', tw_smul']
    simp

theorem conjRep_of : ConjRep := by
  intro σ Γ V _ _ _ _ ξ
  let ξ' : Representation ℂ Γ (Tw σ V) :=
    { toFun := fun g => twMap σ V (ξ g)
      map_one' := by
        ext x
        simp [twMap]
      map_mul' := fun g h => by
        ext x
        simp [twMap, Module.End.mul_apply] }
  exact ⟨Tw σ V, twAdd σ V, twMod σ V, tw_finite σ V, ξ', toTw σ V, tw_smul σ V, fun g x => rfl⟩

end UpperTheory.Gal.LocalSmoothExtension
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxFlat
section
set_option autoImplicit false

noncomputable section

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem sigma_finsum {α : Type} {δ : α → Type} (F : (Σ a, δ a) → ℂ) (S : Finset (Σ a, δ a))
    (hS : ∀ z, F z ≠ 0 → z ∈ S) : ∑ᶠ a, ∑ᶠ d, F ⟨a, d⟩ = ∑ z ∈ S, F z := by
  have hinj : ∀ a, Set.InjOn (Sigma.mk a : δ a → Σ a, δ a) (Sigma.mk a ⁻¹' (S : Set (Σ a, δ a))) :=
    fun a => sigma_mk_injective.injOn
  let U : ∀ a, Finset (δ a) := fun a => S.preimage (Sigma.mk a) (hinj a)
  have h1 : ∀ a, ∑ᶠ d, F ⟨a, d⟩ = ∑ d ∈ U a, F ⟨a, d⟩ := fun a =>
    finsum_eq_sum_of_support_subset _ (fun d hd => by
      simpa [U] using hS _ hd)
  have hT : Function.support (fun a => ∑ᶠ d, F ⟨a, d⟩) ⊆ ((S.image Sigma.fst : Finset α) : Set α) := by
    intro a ha
    have ha' : ∑ d ∈ U a, F ⟨a, d⟩ ≠ 0 := by
      rw [← h1 a]; exact ha
    obtain ⟨d, hd, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha'
    have hd' : (⟨a, d⟩ : Σ a, δ a) ∈ S := by simpa [U] using hd
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hd', rfl⟩)
  rw [finsum_eq_sum_of_support_subset _ hT]
  simp_rw [h1]
  rw [← Finset.sum_sigma (S.image Sigma.fst) U F]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨a, d⟩
  simp only [Finset.mem_sigma, Finset.mem_image, U, Finset.mem_preimage]
  exact ⟨fun h => h.2, fun h => ⟨⟨_, h, rfl⟩, h⟩⟩

private theorem flat_finsum {α : Type} {β γ : α → Type} (n : ∀ a, β a → ℂ) (t : ∀ a, β a → γ a → ℂ)
    (S : Finset (Σ a, β a × γ a)) (hS : ∀ z, t z.1 z.2.1 z.2.2 ≠ 0 → z ∈ S) :
    ∑ᶠ a, ∑ᶠ b, n a b * ∑ᶠ y, t a b y = ∑ z ∈ S, n z.1 z.2.1 * t z.1 z.2.1 z.2.2 := by
  rw [← sigma_finsum (fun z : Σ a, β a × γ a => n z.1 z.2.1 * t z.1 z.2.1 z.2.2) S
    (fun z hz => hS z (right_ne_zero_of_mul hz))]
  refine finsum_congr fun a => ?_
  have hfin : (Function.support fun d : β a × γ a => n a d.1 * t a d.1 d.2).Finite := by
    have hinj : Set.InjOn (fun d : β a × γ a => (⟨a, d⟩ : Σ a, β a × γ a))
        ((fun d : β a × γ a => (⟨a, d⟩ : Σ a, β a × γ a)) ⁻¹' (S : Set (Σ a, β a × γ a))) := by
      intro d _ d' _ h
      simpa using h
    refine (S.finite_toSet.preimage hinj).subset ?_
    intro d hd
    exact hS ⟨a, d⟩ (right_ne_zero_of_mul hd)
  rw [finsum_curry _ hfin]
  refine finsum_congr fun b => ?_
  exact mul_finsum _ _

theorem cxFlat_of : CxFlat := by
  intro p _ G v c K f S hS
  unfold cxTotalM cxSumM cxSumAtM
  refine flat_finsum (α := FCls G) (β := fun q => PtsOf G v K q) (γ := fun q => grp G (Quot.out q).β)
    (fun q a => ((Nat.card (Stab G v (Quot.out q).β (Quot.out q).trivAf.choose
      (Quot.out q).trivAf.choose_spec.choose (Quot.out q).trivAf.choose_spec.choose_spec K (Kp G)
      (Quot.out a)) : ℕ) : ℂ)⁻¹)
    (fun q a y => if FixL G v (Quot.out q).β y (Quot.out a).2.1 then
      f ((Quot.out a).1.1⁻¹ * toAfF G (Quot.out q).β (Quot.out q).trivAf.choose
          (Quot.out q).trivAf.choose_spec.choose (Quot.out q).trivAf.choose_spec.choose_spec y *
          (Quot.out a).1.1) *
        oneP G ((Quot.out a).1.2⁻¹ * toP1 G (Quot.out q).β y * (Quot.out a).1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v (Quot.out q).β y (Quot.out a).2.1)
      else 0) S ?_
  intro z hz
  refine hS z ?_
  beta_reduce at hz
  split_ifs at hz with hfix
  · have h12 := left_ne_zero_of_mul hz
    exact ⟨hfix, left_ne_zero_of_mul h12, right_ne_zero_of_mul h12⟩
  · exact (hz rfl).elim

end UpperTheory.Gal.LocalSmoothExtension
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxLin
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cxLin_of :
    CxFlat → CxLin := by
  intro hflat p _ G v K m f a hfin A w c
  classical
  have hU : (⋃ i, {z : Σ q : GlobalTheory.LKCx.FCls G, PtsOf G v K q × GlobalTheory.LKCx.grp G (Quot.out q).β |
      Seen G v K (f i) z.1 z.2.1 z.2.2}).Finite := Set.finite_iUnion hfin
  have hS : ∀ i z, Seen G v K (f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro i z hz
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨i, hz⟩
  have hS' : ∀ z, Seen G v K (∑ i, a i • f i) z.1 z.2.1 z.2.2 → z ∈ hU.toFinset := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Finset.sum_apply] at h2
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    refine hS i z ⟨h1, ?_, h3⟩
    intro h0
    apply hi
    simp [Pi.smul_apply, smul_eq_mul, h0]
  have hR : ∀ α i, GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) =
      ∑ z ∈ hU.toFinset, summ G v (c α) K (f i) z :=
    fun α i => hflat p G v (c α) K (f i) hU.toFinset (hS i)
  have hT : ∀ z, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z =
      ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := by
    intro z
    unfold summ
    split_ifs with hfix
    · simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    · simp [Finsupp.sum]
  calc GlobalTheory.RootSumWeights.cxTotalM G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) (Kp G) (oneP G)
      = ∑ z ∈ hU.toFinset, summ G v (fun P μ => w.sum fun α r => r * c α P μ) K (∑ i, a i • f i) z :=
        hflat p G v _ K _ hU.toFinset hS'
    _ = ∑ z ∈ hU.toFinset, ∑ i, a i * w.sum fun α r => r * summ G v (c α) K (f i) z :=
        Finset.sum_congr rfl fun z _ => hT z
    _ = ∑ i, ∑ z ∈ hU.toFinset, a i * w.sum fun α r => r * summ G v (c α) K (f i) z := Finset.sum_comm
    _ = ∑ i, a i * w.sum fun α r => r * GlobalTheory.RootSumWeights.cxTotalM G v (c α) K (f i) (Kp G) (oneP G) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finsupp.sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hR α i, Finset.mul_sum]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDPairPol
section
open UpperTheory.Gal.LocalSmoothExtension

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem sim_herm {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β u : G.Cˣ) (s : ℚ)
    (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) :
    (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
      (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
  set a : G.C := algebraMap ℚ G.C s with ha
  have hcomm : ∀ x : G.C, a * x = x * a := fun x => Algebra.commutes s x
  have hsh : sh G (u : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) := by
    rw [← hy]
    simp [mul_assoc]
  have key : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C) = a * ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [hsh]
    calc ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * β) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C)
        = ((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * (a * (u : G.C)) := by
          simp [mul_assoc]
      _ = ((β⁻¹ : G.Cˣ) : G.C) * (((u⁻¹ : G.Cˣ) : G.C) * (u : G.C)) * a := by
          rw [hcomm]; simp only [mul_assoc]
      _ = a * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [hcomm]; simp
  have hpa : G.psi v a = (s : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [ha, IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have hΓ : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v))
  have hUΓ : (G.psi v (u : G.C))ᴴ * G.gram v = G.gram v * G.psi v (sh G (u : G.C)) := by
    rw [show sh G (u : G.C) = MulOpposite.unop (G.star (u : G.C)) from rfl, G.psi_star]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hΓ, Matrix.one_mul]
  calc (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (u : G.C))) := by
        rw [map_mul, map_mul, ← Matrix.mul_assoc, hUΓ]
        simp only [Matrix.mul_assoc]
    _ = (s : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [key, map_mul, hpa, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

private theorem coeff_zero_ne {F A : Type} [Field F] [Ring A] [Algebra F A] [Algebra.IsIntegral F A] [Nontrivial A]
    (g : Aˣ) : (minpoly F (g : A)).coeff 0 ≠ 0 := by
  intro h
  have hint : IsIntegral F (g : A) := Algebra.IsIntegral.isIntegral _
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h
  have hmon : (minpoly F (g : A)).Monic := minpoly.monic hint
  have hqmon : q.Monic := by
    rw [hq] at hmon
    exact Polynomial.monic_X.of_mul_monic_left hmon
  have haeval : Polynomial.aeval (g : A) q = 0 := by
    have h0 := minpoly.aeval F (g : A)
    rw [hq, map_mul, Polynomial.aeval_X] at h0
    have := congrArg (fun y => ((g⁻¹ : Aˣ) : A) * y) h0
    simpa [← mul_assoc] using this
  have hle := minpoly.min F (g : A) hqmon haeval
  rw [hq, Polynomial.degree_mul, Polynomial.degree_X] at hle
  have hq0 : q ≠ 0 := hqmon.ne_zero
  rw [Polynomial.degree_eq_natDegree hq0] at hle
  norm_cast at hle
  omega

theorem dPairPol_of :
    DPairPol := by
  intro p _ G P v
  refine ⟨coeff_zero_ne (F := G.F) (A := G.C) P.γ, (P.c : ℚ), ?_⟩
  intro z hz
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hev : eval₂ v.embedding z (minpoly G.F (P.γ : G.C)) = 0 :=
    (Polynomial.mem_roots_map (minpoly.ne_zero hint)).mp hz
  obtain ⟨x, hx, hMx⟩ := PolyArch.roots_eig_any p G v (P.γ : G.C) z hev
  have hsim := sim_herm G v P.β P.γ (P.c : ℚ) P.sim
  have hform := GlobalTheory.EigenvalueNormSignature.form_mulVec (G.psi v (P.γ : G.C))
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x
  rw [hsim, hMx] at hform
  have hQ : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := P.posR v x hx
    rw [h0] at h1 h2
    simp at h1 h2
    exact h1 h2
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at hform
  apply mul_right_cancel₀ hQ
  rw [Complex.star_def] at hform
  push_cast at hform ⊢
  linear_combination hform

end UpperTheory.Gal.LocalSmoothExtension
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PDSumCongr
section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.dSumCongr_of :
    DSumCongr := by
  classical
  intro p _ G wt wt' s hw K f r K' φ
  unfold GlobalTheory.LKDef.dSumIrr
  rw [mul_comm _ s, ← smul_eq_mul s, smul_finsum]
  refine finsum_congr (fun q => ?_)
  split_ifs
  · rw [smul_eq_mul, hw]
    ring
  · simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGoodConj
section
open UpperTheory.Gal.LocalSmoothExtension
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private lemma map_oneP (σ : ℂ ≃+* ℂ) {p : ℕ} [Fact p.Prime] (G : HTGroup p) (g : Gr G 1) :
    σ (oneP G g) = oneP G g := by
  unfold oneP
  by_cases h : g ∈ (Kp G : Set (Gr G 1))
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

private lemma pointSum_conj (σ : ℂ ≃+* ℂ) {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁)
    (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ)
    (φ : G₂ → ℂ) (hφ : ∀ x, σ (φ x) = φ x) :
    GlobalTheory.LKCount.pointSum ι₁ ι₂ θ K₁ K₂ γ δ (fun g => σ (f g)) φ =
      σ (GlobalTheory.LKCount.pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ) := by
  unfold GlobalTheory.LKCount.pointSum
  refine Eq.trans ?_ (AddEquiv.map_finsum σ.toAddEquiv _).symm
  refine finsum_congr fun q => ?_
  simp [map_mul, map_inv₀, map_natCast, hφ]

private lemma orbC_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (θ : H →* H) (K C : Subgroup H) (δ : H) (F : H → ℂ) :
    GlobalTheory.LKCount.orbC θ K C δ (fun g => σ (F g)) = σ (GlobalTheory.LKCount.orbC θ K C δ F) := by
  unfold GlobalTheory.LKCount.orbC
  refine Eq.trans ?_ (AddEquiv.map_finsum σ.toAddEquiv _).symm
  refine finsum_congr fun q => ?_
  simp [map_mul, map_inv₀, map_ratCast]

theorem UpperTheory.Gal.LocalSmoothExtension.goodConj_of :
    GoodConj := by
  intro σ p _ G K f h
  refine ⟨fun g hg => h.reg g fun h0 => hg (by simp [h0]), fun P hm hi => ?_, fun B x t hx y hy => ?_⟩
  · have h0 := h.pairs P hm hi
    unfold Pair.term at h0 ⊢
    split_ifs at h0 ⊢ with hh
    · unfold Pair.termAt at h0 ⊢
      rw [pointSum_conj σ _ _ _ _ _ _ _ f _ (map_oneP σ G), h0, map_zero]
    · rfl
  · have h0 := h.forms B x t hx y hy
    unfold GlobalTheory.LKCount.orbK at h0 ⊢
    have e : (fun h : G.GAf × Gr G 1 => σ (f h.1) * oneP G h.2) =
        fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2) := by
      funext h
      rw [map_mul, map_oneP]
    rw [e, orbC_conj σ, h0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHExpInj
section
set_option autoImplicit false

namespace UpperTheory.Gal.LocalSmoothExtension

theorem hExpInj_of : HExpInj := by
  intro F _ _ n t₀ ε lam h hanti hh i k hik
  rcases hh with ⟨m, -, hh⟩ | ⟨m, -, hh⟩
  · rw [hh i, hh k] at hik
    have hi := i.isLt
    have hk := k.isLt
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti t₀ hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti t₀ hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega
  · rw [hh i, hh k] at hik
    have si : ∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) i =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have sk : ∑ j ∈ Finset.univ.erase k, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) k =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k)
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega

end UpperTheory.Gal.LocalSmoothExtension
end

