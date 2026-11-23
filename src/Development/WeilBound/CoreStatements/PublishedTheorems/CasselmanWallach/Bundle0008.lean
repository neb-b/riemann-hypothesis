module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0002
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BilinearFormCasimir
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW.ExponentialKSet

variable {n : ℕ}

theorem exp_mem_kset' {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hs : (t • X)ᴴ = -(t • X) := by
      rw [Matrix.conjTranspose_smul, h1]
      simp
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((h2.smul_left t).exp_left).eq

theorem lie_of {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) : X ∈ lieSet ε := by
  show Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0
  rw [h1, Matrix.neg_mul, h2.eq, neg_add_cancel]

theorem commute_Jm {ε : Fin n → Bool} {X : Mx n} (h : ∀ i j, X i j ≠ 0 → ε i = ε j) :
    Commute X (Formalism.REAL.Jm ε) := by
  show X * Jm ε = Jm ε * X
  ext i j
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
  by_cases hx : X i j = 0
  · simp [hx]
  · rw [h i j hx, mul_comm]

theorem single_conjTranspose (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]

theorem single_neg' (a b : Fin n) (c : ℂ) : Matrix.single a b (-c) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.single_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem hasDerivAt_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    {f : ℝ → S} {f' : S} (h : HasDerivAt (fun t => (f t : H)) (f' : H) 0) : HasDerivAt f f' 0 := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  convert h using 2 with t
  show ‖((f t - f 0 - (t - 0) • f' : S) : H)‖ = _
  rw [Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul_of_tower]

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  simp [actM, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem actM_add (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

end Act

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

theorem key (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) {X : Mx n}
    (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (v y : kfin ε σ) :
    B (actM E X v) y = - B v (actM E X y) := by
  have hX : X ∈ lieSet ε := lie_of h1 h2
  have hKt : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Kset ε := exp_mem_kset' h1 h2
  have hKU : ∀ k ∈ Kset ε, k ∈ UJset ε := by
    rintro k ⟨hu, hc⟩
    have h1' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
    calc kᴴ * Formalism.REAL.Jm ε * k = star k * (k * Formalism.REAL.Jm ε) := by
          rw [Matrix.mul_assoc, ← hc]; rfl
      _ = Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hkinv : ∀ t : ℝ, ∀ w : H,
      σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((-t) • X)) w) = w := by
    intro t w
    rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ (hKU _ (hKt t)) _ (hKU _ (hKt (-t))),
      ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, hU.1.1]
    rfl
  obtain ⟨Sv, fv, hv, stv⟩ : IsKFin ε σ (v : H) := v.2
  obtain ⟨Sy, fy, hy, sty⟩ : IsKFin ε σ (y : H) := y.2
  let W : Submodule ℂ H := Sv ⊔ Sy
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_sup Sv Sy
  have stW : ∀ g ∈ Kset ε, ∀ x ∈ W, σ g x ∈ W := by
    intro g hg x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (stv g hg a ha) (sty g hg b hb)
  have hWk : W ≤ kfin ε σ := fun x hx => ⟨W, inferInstance, hx, stW⟩
  have hclosed : IsClosed (W : Set H) := Submodule.closed_of_finiteDimensional W
  have hvW : (v : H) ∈ W := Submodule.mem_sup_left hv
  have hyW : (y : H) ∈ W := Submodule.mem_sup_right hy
  have hder : ∀ x : kfin ε σ,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) x) ((actM E X x : H)) 0 := by
    intro x
    rw [hE X hX x]
    exact GlobalTheory.LowTypeDetermined.hasDerivAt_dRep (G := Formalism.REAL.Jm ε) (hD.1 _ x.2) hX
  have hmemW : ∀ x : kfin ε σ, (x : H) ∈ W → (actM E X x : H) ∈ W := by
    intro x hx
    refine hclosed.mem_of_tendsto (hder x).tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_mem _ (W.sub_mem (stW _ (hKt _) _ hx) (stW _ (hKt _) _ hx))
  let cv : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) v, stW _ (hKt t) _ hvW⟩
  let cy : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) y, stW _ (hKt t) _ hyW⟩
  have hcv : HasDerivAt cv ⟨_, hmemW v hvW⟩ 0 := hasDerivAt_sub W (hder v)
  have hcy : HasDerivAt cy ⟨_, hmemW y hyW⟩ (-0) := by
    rw [neg_zero]
    exact hasDerivAt_sub W (hder y)
  let ι : W →ₗ[ℂ] kfin ε σ := Submodule.inclusion hWk
  let ℓ1 : W →ₗ[ℝ] ℂ :=
    { toFun := fun w => B (ι w) y
      map_add' := fun a b => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        simp [Complex.coe_smul] }
  let ℓ2 : W →ₗ[ℝ] ℂ := ((B v).comp ι).restrictScalars ℝ
  let L1 : W →L[ℝ] ℂ := ⟨ℓ1, LinearMap.continuous_of_finiteDimensional ℓ1⟩
  let L2 : W →L[ℝ] ℂ := ⟨ℓ2, LinearMap.continuous_of_finiteDimensional ℓ2⟩
  have d1 := L1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcv
  have d2 := L2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcy.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)))
  have heq : (L1 ∘ cv) = (L2 ∘ (cy ∘ Neg.neg)) := by
    funext t
    show B (ι (cv t)) y = B v (ι (cy (-t)))
    exact hB _ (hKt t) v (ι (cy (-t))) (ι (cv t)) y rfl (hkinv t y).symm
  rw [heq] at d1
  have hu := d2.unique d1
  rw [neg_one_smul] at hu
  have e1 : ι ⟨_, hmemW v hvW⟩ = actM E X v := Subtype.ext rfl
  have e2 : ι ⟨_, hmemW y hyW⟩ = actM E X y := Subtype.ext rfl
  change B v (ι (-⟨_, hmemW y hyW⟩)) = B (ι ⟨_, hmemW v hvW⟩) y at hu
  rw [map_neg, map_neg, e1, e2] at hu
  rw [← hu]

theorem compact_pair (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) (a b : Fin n) (hab : ε a = ε b)
    (v y : kfin ε σ) : B (E a b v) y = B v (E b a y) := by
  have hsup : ∀ (c d : ℂ) (i j : Fin n),
      (Matrix.single a b c + Matrix.single b a d) i j ≠ 0 → ε i = ε j := by
    intro c d i j h
    by_contra hne
    apply h
    have e1 : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab)
    have e2 : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab.symm)
    simp [Matrix.single_apply, e1, e2]
  have s1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
      -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [star_one, star_neg, single_neg']
    abel
  have s2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [Complex.star_def, Complex.conj_I, single_neg']
    abel
  have k1 := key hU hD hE hB s1 (commute_Jm (hsup 1 (-1))) v y
  have k2 := key hU hD hE hB s2 (commute_Jm (hsup Complex.I Complex.I)) v y
  rw [actM_add, actM_single, actM_single] at k1 k2
  simp only [one_smul, neg_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    map_add, map_neg, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Complex.conj_I, smul_eq_mul,
    RingHom.id_apply, LinearMap.add_apply, LinearMap.neg_apply] at k1 k2
  linear_combination (1 / 2 : ℂ) * k1 + (Complex.I / 2) * k2 +
    ((B (E a b v) y - B v (E a b y) - B v (E b a y) + B (E b a v) y) / 2) * Complex.I_sq

end PositivityTheory.CW.ExponentialKSet

namespace PositivityTheory.CW

open ExponentialKSet in
theorem e2a : E2a := by
  unfold E2a AllIrr
  intro n ε H _ _ _ σ hU hI hD E hE B hB v y
  have hterm : ∀ a b, ε b = ε a → B ((E a b * E b a) v) y = B v ((E a b * E b a) y) := by
    intro a b h
    rw [Module.End.mul_apply, Module.End.mul_apply, compact_pair hU hD hE hB a b h.symm,
      compact_pair hU hD hE hB b a h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
    hterm a b (Finset.mem_filter.mp hb).2

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3B
section
open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

private theorem exp_smul_diagonal_I_single_eq_diagonal_exp {n : ℕ} (a : Fin n) (t : ℝ) :
    NormedSpace.exp (t • (Matrix.diagonal fun j : Fin n => if j = a then Complex.I else 0)) =
      Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext j
  by_cases h : j = a
  · simp [h, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]
  · simp [h]

theorem c3b : HighestWeightIntegral := by
  intro n ε H _ _ _ σ hU _ E hE v a x hv hx
  set Y : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => if j = a then Complex.I else 0 with hY
  have hYG : Y ∈ lieSet ε := by
    show Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0
    rw [hY, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [ite_true, Pi.star_apply]
      split_ifs <;> simp
    · simp [h]
  have hact : ReciprocityTheory.ChartRestriction.DS.actM E Y = Complex.I • E a a := by
    simp [ReciprocityTheory.ChartRestriction.DS.actM, hY, Matrix.diagonal_apply, ite_smul]
  have hv' : (v : H) ≠ 0 := by simpa using hv
  have hD : dRep σ Y (v : H) = (Complex.I * x) • (v : H) := by
    rw [← hE Y hYG v, hact]
    simp only [hx, LinearMap.smul_apply, Submodule.coe_smul]
    rw [mul_smul]
  set u : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 with hu
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • Y) = u t := fun t => exp_smul_diagonal_I_single_eq_diagonal_exp a t
  have huU : ∀ t, u t ∈ UJset ε := by
    intro t
    show (u t)ᴴ * Formalism.REAL.Jm ε * u t = Formalism.REAL.Jm ε
    rw [hu, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [ite_true, Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_comm _ (if ε j = true then (1 : ℂ) else -1), mul_assoc, ← Complex.exp_add]
      simp
    · simp [h]
  have hmul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    simp only [hu, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, add_mul, Complex.exp_add]
    · simp [h]
  have hu0 : u 0 = 1 := by simp [hu]
  have hu2 : u (2 * Real.pi) = 1 := by
    simp only [hu]
    rw [← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, Complex.exp_two_pi_mul_I]
    · simp [h]
  set F : ℝ → H := fun t => σ (u t) (v : H) with hFdef
  have hF : ∀ s t, F (s + t) = σ (u s) (F t) := by
    intro s t
    simp only [hFdef, hmul, hU.1.2 _ (huU s) _ (huU t), ContinuousLinearMap.comp_apply]
  have hx0 : x ≠ 0 → HasDerivAt F ((Complex.I * x) • (v : H)) 0 := by
    intro hx0
    have h1 : deriv F 0 = (Complex.I * x) • (v : H) := by
      have : F = fun t : ℝ => σ (NormedSpace.exp (t • Y)) (v : H) := by
        funext t
        simp only [hFdef, hexp]
      rw [this]
      exact hD
    have hne : deriv F 0 ≠ 0 := by
      rw [h1]
      exact smul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hx0)) hv'
    have hd : DifferentiableAt ℝ F 0 := by
      by_contra hnd
      exact hne (deriv_zero_of_not_differentiableAt hnd)
    rw [← h1]
    exact hd.hasDerivAt
  by_cases hx00 : x = 0
  · exact ⟨0, by simp [hx00]⟩
  have hder0 := hx0 hx00
  set c : ℂ := Complex.I * x with hc
  have hderF : ∀ s, HasDerivAt F (c • F s) s := by
    intro s
    have h2 : HasDerivAt (fun r => F (r - s)) (c • (v : H)) s := by
      have := HasDerivAt.comp_sub_const (f := F) (f' := c • (v : H)) s s (by simpa using hder0)
      simpa using this
    have h3 := ((σ (u s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
    have heq : (fun r => σ (u s) (F (r - s))) = F := by
      funext r
      have := hF s (r - s)
      simp only [add_sub_cancel] at this
      exact this.symm
    have h4 : σ (u s) (c • (v : H)) = c • F s := by
      rw [map_smul]
    have h5 : HasDerivAt (fun r => σ (u s) (F (r - s))) (c • F s) s := by
      convert h3 using 1
      · rfl
      · exact h4.symm
    rwa [heq] at h5
  set G : ℝ → H := fun t => Complex.exp (-c * t) • F t with hG
  have hGd : ∀ t, HasDerivAt G 0 t := by
    intro t
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * t) * (-c)) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (-c)).cexp).comp_ofReal
      simpa using this
    have := h1.smul (hderF t)
    convert this using 1
    symm
    rw [smul_smul, ← add_smul, show Complex.exp (-c * t) * c + Complex.exp (-c * t) * -c = 0 by ring,
      zero_smul]
  have hGc := is_const_of_deriv_eq_zero (fun t => (hGd t).differentiableAt)
    (fun t => (hGd t).deriv) (2 * Real.pi) 0
  have hG0 : G 0 = (v : H) := by
    simp only [hG, hFdef, hu0, hU.1.1, one_apply_eq_self, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  have hG2 : G (2 * Real.pi) = Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) • (v : H) := by
    simp only [hG, hFdef, hu2, hU.1.1, one_apply_eq_self]
  rw [hG2, hG0] at hGc
  have hexp1 : Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have : (Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) - 1) • (v : H) = 0 := by
      rw [sub_smul, hGc, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
  refine ⟨-m, ?_⟩
  have h2 : ((x + m : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    rw [hc] at hm
    push_cast at hm ⊢
    linear_combination (-1 : ℂ) * hm
  rcases mul_eq_zero.1 h2 with h | h
  · have : x + m = 0 := by exact_mod_cast h
    push_cast
    linarith
  · exact absurd h Complex.two_pi_I_ne_zero

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3C
section
namespace PositivityTheory.CW

theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C7
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

theorem c7 : C7 := by
  classical
  intro hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N
  obtain ⟨m, K, I0, hK0, hmax⟩ := hMax n ε (kfin ε σ) E hM N
  obtain ⟨S, C', hS, hC', hbd⟩ := hC4 n ε H σ hU hI hD E hKD m
  refine ⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact x.2
  · intro F hcont hder hgrow B hB hI0 v hv
    let F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ := F ∘ₗ (kfin ε σ).subtype
    have key := hmax F' (fun w => hcont w w.2)
      (fun X hX w g hg => by
        have h1 := hder X hX.1 w w.2 g hg
        show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X)))
          (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0
        rw [hKD X hX.1 w]
        exact h1)
      (fun w => hgrow w w.2) B hB
      (fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩
    calc ‖F v 1‖ = ‖F' ⟨v, hv⟩ 1‖ := rfl
      _ ≤ K * B * ‖((1 + ReciprocityTheory.ChartRestriction.DS.casimirK ε E) ^ m) ⟨v, hv⟩‖ := key
      _ ≤ K * B * (C' * sobNorm σ S v) :=
        mul_le_mul_of_nonneg_left (hbd ⟨v, hv⟩) (mul_nonneg hK0 hB)
      _ = K * C' * B * sobNorm σ S v := by ring

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative
section
open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW.DerivativeRepresentation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_eq_dRep (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : ReciprocityTheory.ChartRestriction.DS.dS σ X w = dRep σ X w := by
  unfold ReciprocityTheory.ChartRestriction.DS.dS dRep
  simp only [Complex.coe_smul]

theorem bridge (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)} (hE : PositivityTheory.CW.KDer ε σ E)
    (v : kfin ε σ) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (a b : Fin n) :
    ((E a b v : kfin ε σ) : H) = ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ]
  set Z : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  have h1 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε Z
  have h2 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε Z
  have hd : E a b = ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε Z) +
      Complex.I • ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε Z) := by
    rw [← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_smul, ← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_add,
      ← ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp, ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_single]
  rw [hd, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hE _ h1 v, hE _ h2 v, dS_eq_dRep, dS_eq_dRep]

end PositivityTheory.CW.DerivativeRepresentation

namespace PositivityTheory.CW

open DerivativeRepresentation in
theorem c2a : CardSubmodulesOfIndexLePow := by
  intro n ε H _ _ _ σ hσ hirr E hE v
  have hsm := (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1
  obtain ⟨S0, hS0f, hvS0, hS0K⟩ := v.2
  have hS0k : ∀ x ∈ S0, IsKFin ε σ x := fun x hx => ⟨S0, hS0f, hx, hS0K⟩
  let S : Submodule ℂ (kfin ε σ) := S0.comap (kfin ε σ).subtype
  let f : S →ₗ[ℂ] S0 :=
    { toFun := fun x => ⟨((x : kfin ε σ) : H), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y h => by
    apply Subtype.ext; apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨S, Module.Finite.of_injective f hf, hvS0, fun a b hab w hw => ?_⟩
  show ((E a b w : kfin ε σ) : H) ∈ S0
  rw [bridge hσ hE w (hsm _ w.2)]
  exact CompanionTheory.D.gk.HC.smE_mem_of_compact_A hσ hS0K hab _ hw

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.D5
section
namespace PositivityTheory.CW

theorem d5 : D5 := by
  intro n ε g hg
  have hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g := hg
  refine ⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g),
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g,
    (ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP hu).1,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end PositivityTheory.CW
end

