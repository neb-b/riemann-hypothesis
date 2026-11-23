module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CuspRapid
section
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_bdd (g : GA E a) :
    BddBelow (Set.range fun γ : GL (Fin a) E => height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩

private theorem qht_nonneg (g : GA E a) : 0 ≤ qht g :=
  le_ciInf fun _ => (height_pos _).le

private theorem decay {φ : Sm E a} (hφ : IsCuspForm φ) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖φ.1 g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  have h0 := KernelIndexFullLattice.brCusp_holds E a φ hφ
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  obtain ⟨C, hC⟩ := exists_norm_le_height_pow_neg_siegel h0 hω hωB ht N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E a γ * g.1 ∈ Reduction.normOneGL (K := E) (n := a) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  have h := hC b hb ρ hρ hs kk hkk _ hγx hxe
  rw [h0.1.isLeftInvariant γ g.1] at h
  have hp := height_pos (AdelicGLn.diagonal E a γ * g.1)
  have hq : qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
    have h1 := ciInf_le (qht_bdd (E := E) (a := a) g.1) γ
    rw [retractOne_coe] at h1
    unfold qht
    rw [retractOne_coe]
    exact h1
  rw [le_mul_inv_iff₀ (pow_pos hp N)] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (qht_nonneg _) hq N) (norm_nonneg _)).trans h

private theorem ev_cmp {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (i : Fin d) :
    ev m g i = (cmp i m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, Submodule.coe_add]
  | tmul φ v => simp [ev, mul_comm]

private theorem cmp_rTensor {d : ℕ} (T : Module.End ℂ (Sm E a)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (i : Fin d) :
    cmp i (T.rTensor _ m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp

private theorem prodA_mem (π : CuspSub E a) (Ξ : AlgRep E a) (l : List (Lie E a)) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ tens Ξ.d π.V) : (l.map (smA Ξ)).prod m ∈ tens Ξ.d π.V := by
  induction l with
  | nil => exact hm
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, mem_tens]
    intro i
    rw [smA_apply, cmp_rTensor]
    exact π.stable (.lie X) _ (mem_tens.1 ih i)

private theorem decay_tens (π : CuspSub E a) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (hm : m ∈ tens d π.V) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ev m g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  choose C hC using fun i => decay (π.cusp _ (mem_tens.1 hm i)) N
  refine ⟨∑ i, C i, fun g => ?_⟩
  have hq : 0 ≤ qht (E := E) (a := a) g.1 ^ N := pow_nonneg (qht_nonneg _) N
  have h1 : ‖ev m g.1‖ ≤ ∑ i, ‖(cmp i m).1 g.1‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_
    rw [ev_cmp]
    exact Finset.single_le_sum (f := fun i => ‖(cmp i m).1 g.1‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  refine (mul_le_mul_of_nonneg_right h1 hq).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => hC i g

end

theorem UpperTheory.V.Lit.Geo.cuspRapid :
    CuspRapid := by
  intro E _ _ _ a π Ξ q ω hω l X N
  exact decay_tens π _ (prodA_mem π Ξ l (ω X) (hω X)) N
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.LieOneEqZero
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_prod (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => f x * h x) g = fun y => chart f g y * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

private def mulOp (u : Sm E a) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun x => u.1 x * φ.1 x, fun g => by
    rw [chart_prod]
    exact (u.2 g).mul (φ.2 g)⟩
  map_add' φ ψ := Subtype.ext (funext fun x => mul_add _ _ _)
  map_smul' c φ := Subtype.ext (funext fun x => mul_left_comm _ c _)

private theorem mulOp_apply (u φ : Sm E a) (g : GA E a) : (mulOp u φ).1 g = u.1 g * φ.1 g := rfl

private theorem lie_mulOp (X : Lie E a) (u φ : Sm E a) :
    lie E a X (mulOp u φ) = mulOp u (lie E a X φ) + mulOp (lie E a X u) φ := by
  refine Subtype.ext (funext fun g => ?_)
  have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
    simpa using chart_val f g 1
  change fderiv ℝ (chart (fun x => u.1 x * φ.1 x) g) (oneL E a) X =
    u.1 g * fderiv ℝ (chart φ.1 g) (oneL E a) X + fderiv ℝ (chart u.1 g) (oneL E a) X * φ.1 g
  rw [chart_prod, fderiv_fun_mul (differentiableAt_chart u.2 g) (differentiableAt_chart φ.2 g), hv, hv]
  simp [mul_comm]

private theorem ev_mulOp {d : ℕ} (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((mulOp u).rTensor _ m) g = u.1 g • ev m g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => rw [LinearMap.rTensor_tmul, ev_tmul, ev_tmul, mulOp_apply, mul_smul]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, smul_add]

private theorem smLie_mulOp (Ξ : AlgRep E a) (X : Lie E a) (u : Sm E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smLie Ξ X ((mulOp u).rTensor _ m) =
      (mulOp u).rTensor _ (smLie Ξ X m) + (mulOp (lie E a X u)).rTensor _ m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    change lie E a X (mulOp u φ) ⊗ₜ[ℂ] v + mulOp u φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v) =
      (mulOp u).rTensor _ (lie E a X φ ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) + mulOp (lie E a X u) φ ⊗ₜ[ℂ] v
    rw [lie_mulOp, map_add (f := _), LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.add_tmul]
    abel
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

private theorem smK_mulOp (Ξ : AlgRep E a) (k : Kinf E a) (u : Sm E a) (hu : act (.cpt k) u = u)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    smK Ξ k ((mulOp u).rTensor _ m) = (mulOp u).rTensor _ (smK Ξ k m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : act (.cpt k) (mulOp u φ) = mulOp (act (.cpt k) u) (act (.cpt k) φ) := rfl
    simp only [smK, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h, hu]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem lie_one_eq_zero (u : Sm E a) (hu : ∀ t g, u.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = u.1 g) :
    lie E a (oneL E a) u = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  let c : ℝ → GL (Fin a) (Cinf E) := fun t =>
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))
  have hc : ∀ t, infGL E a (c t) = GlobalTheory.UnitaryBC.splitCentre E a t := fun _ => rfl
  have hval : ∀ t : ℝ, toL (c t).val = Complex.exp t • oneL E a := fun t => by
    ext i j w
    by_cases h : i = j <;> simp [c, expU, toL, oneL, h, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have h0 : c 0 = 1 := Units.ext (by
    have h := hval 0
    rw [Complex.ofReal_zero, Complex.exp_zero, one_smul] at h
    exact h)
  have hd : HasDerivAt (fun t => toL (c t).val) (oneL E a) 0 := by
    simp only [hval]
    simpa using ((Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal).smul_const (oneL E a)
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve u g c _ h0 hd
  simp only [hc, ← CuspidalL2GL.splitCentre_comm, hu] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem levelFn_mulOp {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} {u φ : Sm E a} (hu : IsCut U u)
    (hφ : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (mulOp u φ) := by
  refine ⟨fun γ g => ?_, fun k hk => ?_, fun m hm => ?_⟩
  · rw [mulOp_apply, mulOp_apply, hu.left, hφ.1]
  · have h : act (.fin k) (mulOp u φ) = mulOp (act (.fin k) u) (act (.fin k) φ) := rfl
    rw [h, hu.level k hk, hφ.2.1 k hk]
  · have h : mulOp (0 : Sm E a) φ = 0 := Subtype.ext (funext fun x => zero_mul _)
    rw [lie_mulOp, lie_one_eq_zero u hu.centre, h, add_zero, hφ.2.2 m hm, map_smul]

private theorem ev_dCo (Ξ : AlgRep E a) {q : ℕ} (ω : Co Ξ q) (X : Fin (q + 1) → Herm E a) (g : GA E a) :
    ev (dCo (smLie Ξ) ω X) g =
      ∑ i : Fin (q + 1), (-1 : ℂ) ^ (i : ℕ) • ev (smLie Ξ (toL (X i).1) (ω (i.removeNth X))) g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

end

theorem UpperTheory.V.Lit.Geo.mulEx :
    MulEx := by
  intro E _ _ _ a U Ξ q u α hu hα
  refine ⟨(((mulOp u).rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap α,
    ⟨fun k => ?_, fun X i hi => ?_, fun X => ?_⟩, fun X g => ev_mulOp u (α X) g, fun X g => ?_⟩
  · intro X
    change (mulOp u).rTensor _ (α _) = smK Ξ k ((mulOp u).rTensor _ (α X))
    rw [smK_mulOp Ξ k u (hu.cpt k), hα.equiv k X]
  · change (mulOp u).rTensor _ (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (mulOp u).rTensor _ (α X) ∈ _
    refine Submodule.span_induction (p := fun m _ => (mulOp u).rTensor _ m ∈ _) ?_ ?_ ?_ ?_ (hα.val X)
    · rintro _ ⟨φ, v, hφ, rfl⟩
      exact Submodule.subset_span ⟨_, v, levelFn_mulOp hu hφ, LinearMap.rTensor_tmul _ _ _ _⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]; exact Submodule.smul_mem _ c hx
  · rw [ev_dCo, ev_dCo, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ • ev (smLie Ξ _ ((mulOp u).rTensor _ (α _))) g = _
    rw [smLie_mulOp, map_add (f := _), Pi.add_apply, ev_mulOp, ev_mulOp, smul_add, smul_comm, mul_smul]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.NormEucSq
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.Lit.Geo

def Scale {ι : Type} (q : ι → ℝ) (N : ℕ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∀ s t : ℝ, 0 < s → s ≤ t → (Summable fun i => Real.exp (-Real.pi * (s * q i))) ∧
    ∑' i, Real.exp (-Real.pi * (s * q i)) ≤ (t / s) ^ N * ∑' i, Real.exp (-Real.pi * (t * q i))

section Inf

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def qf (x : Fin a → Cinf E) : ℝ := ∑ i, ∑ w : InfinitePlace E, ‖x i w‖ ^ 2

def euc : (Fin a → Cinf E) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin a × InfinitePlace E) where
  toFun x := WithLp.toLp 2 fun p => x p.1 p.2
  invFun y := fun i w => y.ofLp (i, w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem norm_euc_sq (x : Fin a → Cinf E) : ‖euc x‖ ^ 2 = qf x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem qf_nonneg (x : Fin a → Cinf E) : 0 ≤ qf x := norm_euc_sq x ▸ sq_nonneg _

def gauss (x : Fin a → Cinf E) : ℝ := Real.exp (-Real.pi * qf x)

def quad (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) : ℝ :=
  ∑ w : InfinitePlace E, (((x ᵥ* p) ⬝ᵥ star x) w).re


variable (E a) in
def poly : Subalgebra ℂ ((Fin a → Cinf E) → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun l : (Fin a → Cinf E) →ₗ[ℝ] ℂ => (l : (Fin a → Cinf E) → ℂ))

def pg (P : (Fin a → Cinf E) → ℂ) (x : Fin a → Cinf E) : ℂ := P x * (gauss x : ℝ)

def sc (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ :=
  Real.exp (-((∑ w : InfinitePlace E, Real.log ‖y.det w‖) / ((a : ℝ) * Fintype.card (InfinitePlace E))))

def msum {ι : Type} (x : ι → Fin a → Cinf E) (P : (Fin a → Cinf E) → ℂ) (y : Lie E a) : ℂ :=
  ∑' i, pg P (x i ᵥ* Matrix.of y)

structure IsLat (L : AddSubgroup (Fin a → Af E)) : Prop where
  isOpen : IsOpen (L : Set (Fin a → Af E))
  isCompact : IsCompact (L : Set (Fin a → Af E))

def vFin (v : Fin a → E) : Fin a → Af E := fun i => algebraMap E (Af E) (v i)

def ptF (g : GA E a) : (Fin a → E) →+ (Fin a → Af E) where
  toFun v := vFin v ᵥ* (GeneralLinearGroup.map (pFin E) g).val
  map_zero' := by
    have h : vFin (0 : Fin a → E) = 0 := funext fun _ => map_zero _
    rw [h, Matrix.zero_vecMul]
  map_add' v v' := by
    have h : vFin (v + v') = vFin v + vFin v' := funext fun _ => map_add _ _ _
    rw [h, Matrix.add_vecMul]

def lat (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : AddSubgroup (Fin a → E) := L.comap (ptF g)

variable [_root_.NumberField.IsTotallyComplex E]

def vInf (v : Fin a → E) : Fin a → Cinf E := fun i => pInf E (algebraMap E (Ad E) (v i))

def pt (g : GA E a) : (Fin a → E) →+ (Fin a → Cinf E) where
  toFun v := vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val
  map_zero' := by
    have h : vInf (0 : Fin a → E) = 0 := funext fun _ => by simp [vInf]
    rw [h, Matrix.zero_vecMul]
  map_add' v v' := by
    have h : vInf (v + v') = vInf v + vInf v' := funext fun _ => by simp [vInf]
    rw [h, Matrix.add_vecMul]

def rt (g : GA E a) : GA E a := (retractOne g : KernelIndexFullLattice.G1 E a).1

def gsum {M : Type} [AddCommMonoid M] [TopologicalSpace M] (L : AddSubgroup (Fin a → Af E)) (F : (Fin a → Cinf E) → M)
    (g : GA E a) : M := ∑' v : lat L g, F (pt (rt g) v.1)

def Th (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : ℝ := gsum L gauss g

def fn (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : ℝ := Real.log (Th L g)

def mean (L : AddSubgroup (Fin a → Af E)) (P : (Fin a → Cinf E) → ℂ) (g : GA E a) : ℂ := gsum L (pg P) g / (Th L g : ℝ)

def mom (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : Herm E a :=
  ⟨Matrix.of fun i j w => mean L (fun x => star (x i w) * x j w) g, by
    change star _ = _
    ext i j w
    simp only [Matrix.star_apply, Matrix.of_apply, Pi.star_apply, mean, gsum, pg, star_div₀, tsum_star, star_mul',
      star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_tsum, map_mul, Complex.conj_conj, mul_comm]⟩

def dev (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : Herm E a :=
  mom L g - ell E a (toL (mom L g).1) • (⟨1, IsSelfAdjoint.one _⟩ : Herm E a)

def meanAlg (L : AddSubgroup (Fin a → Af E)) : Subalgebra ℂ (GA E a → ℂ) :=
  Algebra.adjoin ℂ {f | ∃ P ∈ poly E a, f = mean L P}

end Inf

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped TensorProduct

private theorem hd_map {Γ M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (P : M →ₗ[ℂ] N)
    (b : List Γ → M) : hd (fun z => P (b z)) = fun z => P (hd b z) := by
  funext z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hd, map_sum, map_zsmul]

private theorem zig_map {Γ V S S' : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (G' : Dr.Geo Γ V S' d) (f : S' → S) (P : ∀ q, G.Om q →ₗ[ℂ] G'.Om q)
    (ha : ∀ q γ w, P q (G.act q γ w) = G'.act q γ (P q w))
    (hD : ∀ q w, P (q + 1) (G.dOm q w) = G'.dOm q (P q w))
    (hi : ∀ c, P 0 (G.incl c) = G'.incl (c ∘ f)) (c : List Γ → S → Fin d → ℂ) (q : ℕ) :
    ∀ (k : ℕ) (u : List Γ → G.Om q), Zig G q k u c → Zig G' q k (fun z => P q (u z)) (fun z => c z ∘ f) := by
  induction q with
  | zero =>
    intro k u h z hz
    beta_reduce
    rw [h z hz, hi]
  | succ q ih =>
    rintro k u ⟨b, h1, h2, h3⟩
    refine ⟨fun z => P q (b z), fun γ z hz => ?_, fun z hz => ?_, ?_⟩
    · beta_reduce
      rw [h1 γ z hz, ha]
    · beta_reduce
      rw [← h2 z hz, hD]
    · rw [hd_map]
      exact ih _ _ h3

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def pb (ho : IsOpen (cone E a)) (U U' : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U) (q : ℕ) : (geo ho U Ξ).Om q →ₗ[ℂ] (geo ho U' Ξ).Om q where
  toFun w := ⟨fun s => w.1 (f s), fun s => w.2 (f s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem ev_rT {d : ℕ} (x : GL (Fin a) (Af E)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((act (.fin x)).rTensor (Fin d → ℂ) m) g = ev m (g * finGL E a x) := by
  induction m using TensorProduct.inductionOn with
  | tmul φ v => rfl
  | add m m' h h' => simp only [map_add (f := _), Pi.add_apply, h, h']

private theorem rT_map' {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : A * T = T * A) (m : W ⊗[ℂ] (Fin d → ℂ)) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  induction m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    congr 1
    exact (LinearMap.congr_fun h φ).symm

private theorem cpt_fin (k : Kinf E a) (x : GL (Fin a) (Af E)) :
    act (.cpt k) * act (.fin x) = act (.fin x) * act (E := E) (.cpt k) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem rT_lie (Ξ : AlgRep E a) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smLie Ξ X m) = smLie Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h1 := rT_map' (act (.fin x)) (lie E a X) LinearMap.id (lie_rt_fin X x) m
  have h2 := rT_map' (act (.fin x)) LinearMap.id (Matrix.toLin' (Ξ.dmat X)) rfl m
  change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (_ + _) = _ + _
  rw [map_add (f := _)]
  exact congrArg₂ (· + ·) h1 h2

private theorem lev_fin {U U' : Subgroup (GL (Fin a) (Af E))} {x : GL (Fin a) (Af E)} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U)
    (Ξ : AlgRep E a) {φ : Sm E a} (h : IsLevelFn U Ξ φ) : IsLevelFn U' Ξ (act (.fin x) φ) := by
  refine ⟨fun γ g => ?_, fun u hu => ?_, fun m hm => ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.1]
  · refine Subtype.ext (funext fun g => ?_)
    have e : φ.1 (g * finGL E a x * finGL E a (x⁻¹ * u * x)) = φ.1 (g * finGL E a x) :=
      congrFun (congrArg Subtype.val (h.2.1 _ (hx u hu))) (g * finGL E a x)
    change φ.1 (g * finGL E a u * finGL E a x) = φ.1 (g * finGL E a x)
    rw [← e, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
    congr 3
    group
  · have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin (oneL E a) x) φ
    rw [e, h.2.2 m hm, map_smul]

end

theorem UpperTheory.V.Lit.Geo.perNat :
    PerNat := by
  intro E _ _ _ a U U' x hx Ξ q α hα
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, fun c c' hc h => ?_⟩
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α _) = smK Ξ k ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X))
    rw [hα.equiv k X]
    exact rT_map' _ _ _ (cpt_fin k x) _
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) ∈ _
    have hm := hα.val X
    generalize α X = m at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, v, hφ, rfl⟩ := hy
      exact Submodule.subset_span ⟨_, v, lev_fin hx Ξ hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul s y _ hy => rw [map_smul]; exact Submodule.smul_mem _ s hy
  · refine AlternatingMap.ext fun X => ?_
    change _ = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (dCo (smLie Ξ) α X)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact (rT_lie Ξ x _ _).symm
  · obtain ⟨ho, w, hw, hz⟩ := h
    let f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U := fun s =>
      Quotient.liftOn' s (fun y => ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) fun y y' hy => by
        rw [QuotientGroup.leftRel_apply] at hy
        refine QuotientGroup.eq.2 ?_
        have := hx _ hy
        rwa [show (y * x)⁻¹ * (y' * x) = x⁻¹ * (y⁻¹ * y') * x by group]
    have hf : ∀ (g : GL (Fin a) (Af E)) s, f (g • s) = g • f s := fun g s => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      change ((g * y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) = ((g * (y * x) : GL (Fin a) (Af E)) : _ ⧸ U)
      rw [mul_assoc]
    have hc' : c' = fun z => c z ∘ f := by
      funext z s
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      exact hc z y
    refine ⟨ho, pb ho U U' Ξ f q w, fun g y X => ?_, ?_⟩
    · change w.1 ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) _ _ =
        Ξ.mat g *ᵥ ev ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X)) _
      rw [ev_rT, mul_assoc, ← map_mul]
      exact hw g (y * x) X
    · rw [hc']
      refine zig_map (geo ho U Ξ) (geo ho U' Ξ) f (pb ho U U' Ξ f) (fun q γ w => ?_) (fun q w => rfl) (fun c => rfl) c q 0 _ hz
      refine Subtype.ext (funext fun s => funext fun p => ContinuousAlternatingMap.ext fun v => ?_)
      change _ *ᵥ w.1 ((geo ho U Ξ).σ γ⁻¹ (f s)) _ _ = _ *ᵥ w.1 (f ((geo ho U' Ξ).σ γ⁻¹ s)) _ _
      rw [geo_σ, geo_σ, hf]
      rfl
end

