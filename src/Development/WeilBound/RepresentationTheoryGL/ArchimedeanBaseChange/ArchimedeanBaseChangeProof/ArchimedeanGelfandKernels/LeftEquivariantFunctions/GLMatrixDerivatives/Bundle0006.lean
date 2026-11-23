module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcB
section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hb_conj_back (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = X := by
  have h : (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = ((k.1)ᴴ * k.1) * X * ((k.1)ᴴ * k.1) := by
    simp only [Matrix.mul_assoc]
  rw [h, unit_star_mul]
  simp

theorem dCinCE : DCinCE := by
  intro n lam E Fr ε ι S Γ T hD f hf
  obtain ⟨hs, heq⟩ := hf
  have hdiff : ∀ x ∈ GLs n, DifferentiableAt ℝ f x := fun x hx =>
    (hs.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)
  refine ⟨?_, ?_⟩
  · have hfa := contDiffOn_fderivWithin_apply (m := ∞) hs isOpen_GLs.uniqueDiffOn (le_of_eq rfl)
    unfold DC
    refine ContDiffOn.sum fun p _ => ?_
    have h1 : ContDiffOn ℝ ∞ (fun x => Rd (hb p) f x) (GLs n) := by
      refine (hfa.comp (contDiffOn_id.prodMk (mulRL (hb p)).contDiff.contDiffOn)
        (fun x hx => ⟨hx, Set.mem_univ _⟩)).congr fun x hx => ?_
      show fderiv ℝ f x (x * hb p) = fderivWithin ℝ f (GLs n) x (mulRL (hb p) x)
      rw [fderivWithin_of_isOpen isOpen_GLs hx, mulRL_apply]
    have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Fr 1 (hb p) (f x)) (GLs n) :=
      ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hs
    exact ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (h1.add h2)
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := mem_GLs_mul hg (unit_mem k)
    have hRd : ∀ X : Mat n, Rd X f (g * k.1) = E.ρ k⁻¹ (Rd (k.1 * X * (k.1)ᴴ) f g) := by
      intro X
      have hev : (fun y : Mat n => f (y * k.1)) =ᶠ[nhds g]
          fun y => ((E.ρ k⁻¹).restrictScalars ℝ) (f y) := by
        filter_upwards [isOpen_GLs.mem_nhds hg] with y hy
        simpa using heq y hy k
      have h := fderiv_right f k.1 g _ (hdiff _ hgk) (hdiff _ hg) hev (g * (k.1 * X * (k.1)ᴴ))
      have hm : g * (k.1 * X * (k.1)ᴴ) * k.1 = g * k.1 * X := by
        simp only [Matrix.mul_assoc, unit_star_mul, Matrix.mul_one]
      show fderiv ℝ f (g * k.1) (g * k.1 * X) = E.ρ k⁻¹ (fderiv ℝ f g (g * (k.1 * X * (k.1)ᴴ)))
      rw [← hm]
      simpa using h
    have hv : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, rho_mul_inv]
      rfl
    have hdF : ∀ (X : Mat n) (v : E.V), (fderiv ℝ Fr 1 X) (E.ρ k⁻¹ v)
        = E.ρ k⁻¹ (fderiv ℝ Fr 1 (k.1 * X * (k.1)ᴴ) v) := by
      intro X v
      have h := dFr_conj hD k (k.1 * X * (k.1)ᴴ)
      rw [hb_conj_back k X] at h
      rw [h, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hv]
    have heps : ∀ (X : Mat n), IsHermitian X → ∀ w,
        ε X (E.ρ k⁻¹ w) = E.ρ k⁻¹ (ε (k.1 * X * (k.1)ᴴ) w) := by
      intro X hX w
      rw [← ContinuousLinearMap.mul_apply, eps_rho_inv hD k X hX, ContinuousLinearMap.mul_apply]
    let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] E.V :=
      LinearMap.mk₂ ℝ (fun Y Z => ε Y (Rd Z f g + fderiv ℝ Fr 1 Z (f g)))
        (by
          intro a b c
          simp only [map_add (f := _), ContinuousLinearMap.add_apply]
          abel)
        (by intro c a b; simp only [map_smul, ContinuousLinearMap.smul_apply])
        (by
          intro a b c
          simp only [Rd, Matrix.mul_add, map_add (f := _), ContinuousLinearMap.add_apply]
          abel)
        (by
          intro c a b
          simp only [Rd, Matrix.mul_smul, map_smul, ContinuousLinearMap.smul_apply]
          rw [← smul_add]
          exact (ε a).map_smul_of_tower c _)
    have key := basis_inv B k
    unfold DC
    rw [heq g hg k]
    calc ∑ p : Fin n × Fin n, ε (hb p) (Rd (hb p) f (g * k.1) + fderiv ℝ Fr 1 (hb p) (E.ρ k⁻¹ (f g)))
        = ∑ p : Fin n × Fin n, E.ρ k⁻¹ (B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRd, hdF, ← map_add (f := _), heps _ (hb_herm p)]
          rfl
      _ = E.ρ k⁻¹ (∑ p : Fin n × Fin n, B (hb p) (hb p)) := by rw [← map_sum, key]
      _ = _ := rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfGam
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Gam

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem iteratedDeriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (k : ℕ)
    (t : ℝ) : iteratedDeriv k (fun s => A (φ s)) t = A (iteratedDeriv k φ t) := by
  have h := (A.restrictScalars ℝ).iteratedFDeriv_comp_left (f := φ) (x := t) (i := k)
  have h2 := congrArg (fun L => L (fun _ : Fin k => (1 : ℝ))) h
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h2
  exact h2

theorem deriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (t : ℝ) :
    deriv (fun s => A (φ s)) t = A (deriv φ t) := by
  have := iteratedDeriv_equiv A φ 1 t
  simpa only [iteratedDeriv_one] using this

theorem wave_equiv (E : KMod n) (A : E.V ≃L[ℂ] E.V) (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v))
    (u : ℝ → Mat n → E.V) (hu : IsWave E u) : IsWave E fun t x => A (u t x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn h1
  · intro t
    refine ⟨(A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn (h2 t).1, ?_⟩
    intro g hg k
    simp only
    rw [(h2 t).2 g hg k, hA]
  · intro t g hg
    rw [iteratedDeriv_equiv A (fun s => u s g) 2 t, h3 t g hg, om_equiv]
  · intro g hg
    rw [deriv_equiv A (fun s => u s g) 0, h4 g hg, map_zero]

theorem act_equiv (hWE : WaveEx) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : E.V ≃L[ℂ] E.V)
    (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v)) (w : List (Bool × ℕ)) (g : ℝ → ℝ)
    (ks : Mat n → (E.V →L[ℂ] E.V)) (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (fun x => A (f x)) 1 = A (act μ E ks f 1) := by
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have hAu := wave_equiv E A hA u hu
  have hone : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have key : ∀ F F' : Mat n → E.V, Set.EqOn F F' (GLs n) → act μ E ks F 1 = act μ E ks F' 1 := by
    intro F F' h
    unfold act
    congr 1
    funext y
    rw [h]
    simp only [GLs, Set.mem_setOf_eq, one_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  rw [key (fun x => A (f x)) (fun x => A (u 0 x)) (fun x hx => by simp only [hu0 x hx]),
    key f (u 0) (fun x hx => (hu0 x hx).symm),
    hks.2.2.2 _ hAu 1 hone, hks.2.2.2 _ hu 1 hone]
  refine Eq.trans ?_ (congrFun (zop_equiv A w _) 1)
  congr 2
  funext x'
  rw [← A.integral_comp_comm]
  congr 1
  funext t
  exact ((A : E.V →L[ℂ] E.V).map_smul_of_tower (g t) (u t x')).symm

end PositivityTheory.RgBcC.LfSt.ChainPf.Gam
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.HermInvConj
section
noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcHalf1

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_single (i : Fin n × Fin n) : hOf (Pi.single i (1 : ℝ)) = hb i := by
  simp only [hOf]
  rw [Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · simp

theorem herm_inv_conj {x H : Mat n} (hH : H.IsHermitian) : (x⁻¹ * H * xᴴ⁻¹).IsHermitian := by
  rw [← conjTranspose_nonsing_inv]
  exact isHermitian_mul_mul_conjTranspose _ hH

def phiL {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Fr k : Mat n → (V →L[ℂ] V)) (w : Mat n) :
    Mat n →ₗ[ℝ] (V →L[ℂ] V) where
  toFun X := fderiv ℝ Fr 1 X * k w + Ld X k w
  map_add' X Y := by
    simp only [Ld, map_add (f := _), add_mul, Matrix.add_mul, neg_add]
    abel
  map_smul' r X := by
    simp only [Ld, map_smul, smul_mul_assoc, Matrix.smul_mul, RingHom.id_apply, smul_add, smul_neg]

private theorem smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero (hH : HbFacts) {H : Mat n} (h : H.IsHermitian) :
    ∑ p, coords H p • hb p = H := by
  conv_rhs => rw [← (hH n).2.2.1 H h]
  unfold hOf
  refine Finset.sum_congr rfl fun p _ => ?_
  ext a b
  simp [Complex.real_smul]

private theorem trace_mul_mul_mul_rotate_two (a B c D : Mat n) : trace (a * B * c * D) = trace (c * D * a * B) := by
  rw [Matrix.mul_assoc (a * B) c D, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

private theorem exists_dual_basis_dlog_of_isCoord (hH : HbFacts) {W : Type*} [Ring W] [Module ℝ W] [IsScalarTower ℝ W W]
    [SMulCommClass ℝ W W] (α β : Mat n →ₗ[ℝ] W) {x : Mat n} (hx : x.det ≠ 0) :
    ∑ i, α (xᴴ * hb i * x) * β (x⁻¹ * hb i * xᴴ⁻¹) = ∑ p, α (hb p) * β (hb p) := by
  have hbh : ∀ p, (hb p).IsHermitian := (hH n).1
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have huH : IsUnit xᴴ.det := by
    rw [det_conjTranspose]
    exact hu.star
  have hA' : ∀ i, (x⁻¹ * hb i * xᴴ⁻¹).IsHermitian := fun i => by
    rw [← conjTranspose_nonsing_inv]
    exact isHermitian_mul_mul_conjTranspose _ (hbh i)
  have hQ : ∀ q, (xᴴ⁻¹ * hb q * x⁻¹).IsHermitian := fun q => by
    rw [← conjTranspose_nonsing_inv]
    exact isHermitian_conjTranspose_mul_mul _ (hbh q)
  have hexp : ∀ i, β (x⁻¹ * hb i * xᴴ⁻¹) = ∑ q, coords (x⁻¹ * hb i * xᴴ⁻¹) q • β (hb q) := by
    intro i
    conv_lhs => rw [← smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero hH (hA' i)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul]
  have hcoef : ∀ i q, coords (x⁻¹ * hb i * xᴴ⁻¹) q = coords (xᴴ⁻¹ * hb q * x⁻¹) i := by
    intro i q
    simp only [coords]
    rw [trace_mul_mul_mul_rotate_two]
  calc ∑ i, α (xᴴ * hb i * x) * β (x⁻¹ * hb i * xᴴ⁻¹)
      = ∑ i, ∑ q, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (α (xᴴ * hb i * x) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hexp i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hcoef, mul_smul_comm]
    _ = ∑ q, ∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (α (xᴴ * hb i * x) * β (hb q)) := Finset.sum_comm
    _ = ∑ q, α (∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (xᴴ * hb i * x)) * β (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_mul_assoc]
    _ = ∑ p, α (hb p) * β (hb p) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hs : ∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • (xᴴ * hb i * x)
            = xᴴ * (∑ i, coords (xᴴ⁻¹ * hb q * x⁻¹) i • hb i) * x := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mul_smul, Matrix.smul_mul]
        rw [hs, smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero hH (hQ q)]
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ huH, Matrix.one_mul]

set_option maxHeartbeats 800000 in
theorem halfOne_of (hH : HbFacts) (hF : FrameDer) (hO : ∀ n, IsOpen (cone n)) (h1 : DerOne) : HalfOne := by
  intro n lam E Fr ε ι S Γ T hcx σ hσ hσh k hk hkeq d hd c v hv w hw
  obtain ⟨hxG, hdetv⟩ := KcInv.coneGL n σ hσh v hv
  obtain ⟨hyG, hdetw⟩ := KcInv.coneGL n σ hσh w hw
  set F : Mat n → (E.V →L[ℂ] E.V) := fun x' => Kf Fr k Γ T d x' (σ w) with hFdef
  have hFs : ContDiffOn ℝ ∞ F (GLs n) := by
    have hinner : ContDiffOn ℝ ∞ (fun x' : Mat n => x'⁻¹ * d * (σ w)ᴴ⁻¹) (GLs n) :=
      KcInv.mul_contDiffOn (KcInv.mul_contDiffOn KcInv.inv_contDiffOn contDiffOn_const)
        contDiffOn_const
    have hmaps : Set.MapsTo (fun x' : Mat n => x'⁻¹ * d * (σ w)ᴴ⁻¹) (GLs n) (GLs n) :=
      fun x' hx' => KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx') hd)
        (KcInv.inv_mem (KcInv.conjT_mem hyG))
    have h2 := hk.comp hinner hmaps
    exact (((hcx.smooth.mul h2).mul contDiffOn_const).mul contDiffOn_const).mul contDiffOn_const
  have hFinv : ∀ x' ∈ GLs n, ∀ u : unitaryGroup (Fin n) ℂ, F (x' * ↑u) = F x' := by
    intro x' hx' u
    have hu1 : ((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) * (u : Mat n) = 1 := by simp
    have huG : (u : Mat n) ∈ GLs n := by
      show (u : Mat n).det ≠ 0
      intro h0
      have h3 := congrArg Matrix.det hu1
      rw [det_mul, h0, mul_zero, det_one] at h3
      exact zero_ne_one h3
    have hinvu : (u : Mat n)⁻¹ = ((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) :=
      Matrix.inv_eq_left_inv hu1
    have hmG : x'⁻¹ * d * (σ w)ᴴ⁻¹ ∈ GLs n :=
      KcInv.mul_mem (KcInv.mul_mem (KcInv.inv_mem hx') hd) (KcInv.inv_mem (KcInv.conjT_mem hyG))
    have hk' : k (((u⁻¹ : unitaryGroup (Fin n) ℂ) : Mat n) * x'⁻¹ * d * (σ w)ᴴ⁻¹)
        = E.ρ u⁻¹ * k (x'⁻¹ * d * (σ w)ᴴ⁻¹) := by
      have h := hkeq _ hmG u⁻¹ 1
      rw [show ((1 : unitaryGroup (Fin n) ℂ) : Mat n) = 1 from rfl, Matrix.mul_one, map_one,
        mul_one] at h
      rw [← h]
      simp only [Matrix.mul_assoc]
    simp only [hFdef, Kf]
    rw [hcx.mul x' hx' _ huG, hcx.onK u, Matrix.mul_inv_rev, hinvu, hk',
      ← mul_assoc (Fr x' * E.ρ u), mul_assoc (Fr x'), ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hDσ : ContDiffOn ℝ ∞ (fun w' => F (σ w')) (cone n) :=
    hFs.comp hσ (fun v' hv' => (KcInv.coneGL n σ hσh v' hv').1)
  have hDσd : DifferentiableAt ℝ (fun w' => F (σ w')) v :=
    (hDσ.contDiffAt ((hO n).mem_nhds hv)).differentiableAt (by simp)
  have hKc : ∀ e, (fderiv ℝ (Kc σ c Fr k Γ T d) (v, w)) (e, 0)
      = ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (fderiv ℝ (fun w' => F (σ w')) v) e := by
    have hKs := KcInv.kcSmooth n E.V σ c Fr k Γ T d hd hσ hσh hcx.smooth hk
    have hmem : cone n ×ˢ cone n ∈ nhds (v, w) := ((hO n).prod (hO n)).mem_nhds ⟨hv, hw⟩
    have hKd : DifferentiableAt ℝ (Kc σ c Fr k Γ T d) (v, w) :=
      (hKs.contDiffAt hmem).differentiableAt (by simp)
    have h1 := hKd.hasFDerivAt.comp v (hasFDerivAt_prodMk_left (𝕜 := ℝ) v w)
    have h2 := hDσd.hasFDerivAt.const_smul ((c : ℂ) * ((hOf w).det ^ n)⁻¹)
    have heq : (Kc σ c Fr k Γ T d) ∘ (fun e => (e, w))
        = fun v' => ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • F (σ v') := by
      funext v'
      rfl
    rw [heq] at h1
    intro e
    have h3 := congrArg (fun L => L e) (h1.unique h2)
    simpa using h3
  have hfr := hF n (E.V →L[ℂ] E.V) σ F hσ hσh hFs hFinv v hv (σ v) hxG (hσh v hv)
  set x := σ v with hxdef
  set y := σ w with hydef
  set m := x⁻¹ * d * yᴴ⁻¹ with hmdef
  set C : ℂ := (c : ℂ) * ((hOf w).det ^ n)⁻¹ with hCdef
  set φ := phiL Fr k m with hφ
  have hbh := (hH n).1
  have hstep : ∀ i, (fderiv ℝ (fun w' => F (σ w')) v) (Pi.single i 1)
      = (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹) := by
    intro i
    have hXi : (x⁻¹ * hb i * xᴴ⁻¹).IsHermitian := herm_inv_conj (hbh i)
    have hxX : x * (x⁻¹ * hb i * xᴴ⁻¹) * xᴴ = hb i := by
      have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hxG
      have huH : IsUnit xᴴ.det := by
        rw [det_conjTranspose]
        exact hu.star
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ huH, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    have hc1 : coords (hb i) = Pi.single i 1 := by
      have h6 := (hH n).2.2.2.1 (Pi.single i 1)
      rwa [hOf_single] at h6
    have hc2 : coords (hb i + hb i) = Pi.single i 1 + Pi.single i 1 := by
      rw [← hc1]
      funext p
      simp only [coords, Matrix.add_mul, Matrix.trace_add, Complex.add_re, Pi.add_apply]
    have h5 := hfr _ hXi
    rw [hxX] at h5
    first
      | rw [two_smul] at h5
      | rw [two_nsmul] at h5
    rw [hc2, map_add (f := _)] at h5
    have hder : (fderiv ℝ F x) (x * (x⁻¹ * hb i * xᴴ⁻¹))
        = Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹ :=
      h1 n lam E Fr ε ι S Γ T hcx k hk d y hd hyG x hxG _
    rw [hder] at h5
    rw [← h5, ← two_smul ℝ, smul_smul]
    norm_num
  have hfe : ∀ i, ε (hb i) * Fr x = Fr x * ε (xᴴ * hb i * x) :=
    fun i => hcx.frε x hxG (hb i) (hbh i)
  have hdual := exists_dual_basis_dlog_of_isCoord hH ε φ hxG
  rw [show (∑ i, ε (hb i) * (fderiv ℝ (Kc σ c Fr k Γ T d) (v, w)) (Pi.single i 1, 0))
      = ∑ i, ε (hb i) * (C • (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹)) from
      Finset.sum_congr rfl fun i _ => by rw [hKc, hstep]]
  calc ∑ i, ε (hb i) * (C • (1/2 : ℝ) • (Fr x * φ (x⁻¹ * hb i * xᴴ⁻¹) * Γ * T * Fr y⁻¹))
      = C • (1/2 : ℝ) • (Fr x * (∑ i, ε (xᴴ * hb i * x) * φ (x⁻¹ * hb i * xᴴ⁻¹)) * Γ * T
          * Fr y⁻¹) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.smul_sum,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, mul_smul_comm]
        congr 2
        simp only [← mul_assoc]
        rw [hfe i]
    _ = _ := by
        rw [hdual, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
        congr 1
        rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.coe_smul]
        rfl

end PositivityTheory.RgBcC.LfSt.Kchain.KcHalf1
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbCurve
section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbCurve

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain.KbBase
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hasDerivAt_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : HasDerivAt A A' t) (a b : Fin n) :
    HasDerivAt (fun s => A s a b) (A' a b) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b

theorem hasDerivAt_of_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t) :
    HasDerivAt A A' t :=
  hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b

theorem hasDerivAt_matmul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ} (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_of_entry
  intro a b
  have hsum : HasDerivAt (fun s => ∑ k, A s a k * B s k b)
      (∑ k, (A' a k * B t k b + A t a k * B' k b)) t :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_entry hA a k).mul (hasDerivAt_entry hB k b)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using hsum

theorem hasDerivAt_line (X : Mat n) : HasDerivAt (fun t : ℝ => 1 + t • X) X 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
  simp only [id, one_smul] at h
  exact h

theorem det_line_ne (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, (1 + t • X).det ≠ 0 := by
  have hc : Continuous fun t : ℝ => (1 + t • X).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0:ℝ) • X).det ≠ 0 := by simp
  exact hc.continuousAt.eventually_ne h0

theorem hasDerivAt_lineInv (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  set B : ℝ → Mat n := fun t => (1 + t • X)⁻¹ with hB
  have hB0 : B 0 = 1 := by simp [hB]
  have hcont : ContinuousAt B 0 := by
    have hline : Continuous fun t : ℝ => (1 : Mat n) + t • X :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hdet : ContinuousAt Ring.inverse ((1 : Mat n) + (0:ℝ) • X).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (by simp)
    have h2 : ContinuousAt (fun t : ℝ => (1 : Mat n) + t • X) 0 := hline.continuousAt
    exact ContinuousAt.comp (g := Inv.inv) (f := fun t : ℝ => (1 : Mat n) + t • X)
      (continuousAt_matrix_inv _ hdet) h2
  have hlim : Tendsto (fun t => -(B t * X)) (𝓝[≠] (0:ℝ)) (𝓝 (-X)) := by
    have h1 : Tendsto (fun t => -(B t * X)) (𝓝 (0:ℝ)) (𝓝 (-(B 0 * X))) :=
      ((hcont.mul continuousAt_const).neg)
    rw [hB0, one_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine hasDerivAt_iff_tendsto_slope.mpr (hlim.congr' ?_)
  have hne : ∀ᶠ t in 𝓝[≠] (0:ℝ), (1 + t • X).det ≠ 0 :=
    (det_line_ne X).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne, self_mem_nhdsWithin] with t ht ht0
  have hinv : B t * (1 + t • X) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  rw [mul_add, mul_one, Matrix.mul_smul] at hinv
  have ht0' : t ≠ 0 := ht0
  rw [slope_def_module, hB0, sub_zero, ← hinv, sub_add_cancel_left, smul_neg, smul_smul,
    inv_mul_cancel₀ ht0', one_smul]

theorem hasDerivAt_detLine (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X).det) X.trace 0 := by
  set p : Polynomial ℂ := (1 + (Polynomial.X : Polynomial ℂ) • X.map Polynomial.C).det with hp
  have hev : ∀ t : ℝ, (1 + t • X).det = p.eval (t : ℂ) := by
    intro t
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, Complex.real_smul] <;> ring
  have hd : HasDerivAt (fun y : ℝ => p.eval (y : ℂ)) (p.derivative.eval ((0:ℝ) : ℂ)) 0 :=
    (p.hasDerivAt ((0:ℝ) : ℂ)).comp_ofReal
  rw [Complex.ofReal_zero, hp, Matrix.derivative_det_one_add_X_smul] at hd
  rw [show (fun t : ℝ => (1 + t • X).det) = fun y : ℝ => p.eval (y : ℂ) from funext hev]
  exact hd

end PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
end
end

