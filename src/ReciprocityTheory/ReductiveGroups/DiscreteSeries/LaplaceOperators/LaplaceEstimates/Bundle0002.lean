module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0015
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapValA
section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Grp

def jAdj (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Jm ε * gᴴ * Jm ε

lemma jAdj_mul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : jAdj ε g * g = 1 := by
  unfold jAdj
  unfold inUJ at hg
  rw [show Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) by simp only [Matrix.mul_assoc], hg,
    SmDerA.Jm_mul_Jm]

lemma mul_jAdj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * jAdj ε g = 1 :=
  mul_eq_one_comm.mp (jAdj_mul hg)

lemma inUJ_jAdj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inUJ ε (jAdj ε g) := by
  have h1 := mul_jAdj hg
  unfold jAdj at h1 ⊢
  unfold inUJ
  have h2 : g * (Jm ε * (gᴴ * Jm ε)) = 1 := by simpa only [Matrix.mul_assoc] using h1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, SmDerA.Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, LemK.ta_Jm_Jm]
  rw [h2, Matrix.mul_one]

lemma inUJ_one (ε : Fin n → Bool) : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inUJ
  simp

lemma inUJ_exp (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have := LemK.ta_inUJ_mul_exp ε (inUJ_one ε) hX t
  simpa using this

end Grp

section Unit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma inner_sig_sig (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := fun v => hσ.2.1 g hg v }
  exact T.inner_map_map x y

lemma sig_sig_jAdj (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (y : H) :
    σ g (σ (jAdj ε g) y) = y := by
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg _ (inUJ_jAdj hg), mul_jAdj hg, hσ.1.1]
  rfl

lemma inner_sig_left (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (x y : H) : ⟪σ g x, y⟫_ℂ = ⟪x, σ (jAdj ε g) y⟫_ℂ := by
  conv_lhs => rw [← sig_sig_jAdj hσ hg y]
  exact inner_sig_sig hσ hg _ _

lemma hasDerivAt_coef (hσ : IsURepOn (UJset ε) σ) {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) (hX : inG ε X) (y : H) (x : D) :
    HasDerivAt (fun t : ℝ => ⟪y, σ (g * NormedSpace.exp ((t : ℂ) • X)) (x : H)⟫_ℂ)
      ⟪y, σ g ((actM E X x : D) : H)⟫_ℂ 0 := by
  have e : (fun t : ℝ => ⟪y, σ (g * NormedSpace.exp ((t : ℂ) • X)) (x : H)⟫_ℂ) =
      fun t : ℝ => (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ)
        (σ (NormedSpace.exp ((t : ℂ) • X)) (x : H)) := by
    funext t
    rw [hσ.1.2 g hg _ (inUJ_exp ε hX t)]
    rfl
  rw [e]
  exact (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hD.deriv X hX x)

end Unit

section Op

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {D : Submodule ℂ H} {V : Submodule ℂ D}

abbrev ob (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W := stdOrthonormalBasis ℂ W

def opC (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : V ≃ₗ[ℂ] W)
    (h : Matrix (Fin n) (Fin n) ℂ) (B : Module.End ℂ D) : W →L[ℂ] W :=
  ∑ i, ∑ j, ⟪(((ι.symm (ob W i) : V) : D) : H), σ h ((B ((ι.symm (ob W j) : V) : D) : D) : H)⟫_ℂ •
    (innerSL ℂ (ob W j)).smulRight (ob W i)

variable (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : V ≃ₗ[ℂ] W)

lemma opC_add (h : Matrix (Fin n) (Fin n) ℂ) (B₁ B₂ : Module.End ℂ D) :
    opC σ ι h (B₁ + B₂) = opC σ ι h B₁ + opC σ ι h B₂ := by
  simp only [opC, LinearMap.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, add_smul,
    Finset.sum_add_distrib]

lemma opC_smul (h : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (B : Module.End ℂ D) :
    opC σ ι h (c • B) = c • opC σ ι h B := by
  simp only [opC, LinearMap.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_smul,
    Finset.smul_sum]

lemma opC_zero (h : Matrix (Fin n) (Fin n) ℂ) : opC σ ι h (0 : Module.End ℂ D) = 0 := by
  simpa using opC_smul σ ι h (0 : ℂ) 0

def opL (h : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ D →ₗ[ℂ] (W →L[ℂ] W) where
  toFun := opC σ ι h
  map_add' := opC_add σ ι h
  map_smul' := opC_smul σ ι h

lemma vec_expand (v : V) :
    ((v : D) : H) = ∑ j, ⟪ob W j, ι v⟫_ℂ • (((ι.symm (ob W j) : V) : D) : H) := by
  conv_lhs => rw [← ι.symm_apply_apply v, ← (ob W).sum_repr' (ι v)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]

lemma vec_expandD (v : V) :
    (v : D) = ∑ j, ⟪ob W j, ι v⟫_ℂ • ((ι.symm (ob W j) : V) : D) := by
  conv_lhs => rw [← ι.symm_apply_apply v, ← (ob W).sum_repr' (ι v)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]

lemma opC_coef (h : Matrix (Fin n) (Fin n) ℂ) (B : Module.End ℂ D) (v v' : V) :
    ⟪ι v', opC σ ι h B (ι v)⟫_ℂ = ⟪((v' : D) : H), σ h ((B v : D) : H)⟫_ℂ := by
  rw [vec_expandD ι v, vec_expand ι v']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [opC, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, inner_conj_symm]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Op

section Deriv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {D : Submodule ℂ H} {V : Submodule ℂ D} {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
  (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (ι : V ≃ₗ[ℂ] W)

include hσ hD

lemma hasDerivAt_opC {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X)
    (B : Module.End ℂ D) :
    HasDerivAt (fun t : ℝ => opC σ ι (g * NormedSpace.exp ((t : ℂ) • X)) B)
      (opC σ ι g (actM E X * B)) 0 := by
  unfold opC
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_coef hσ hD hg hX _ _).smul_const _

lemma rdV_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hX : inG ε X) : Formalism.REAL.RdV X F g = opC σ ι g (actM E X * B) := by
  have e : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => opC σ ι (g * NormedSpace.exp ((t : ℂ) • X)) B :=
    funext fun t => hF _ (LemK.ta_inUJ_mul_exp ε hg hX t)
  show deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [e]
  exact (hasDerivAt_opC hσ hD ι hg hX B).deriv

lemma eabV_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (a b : Fin n) : Formalism.REAL.EabV ε a b F g = opC σ ι g (E a b * B) := by
  have h1 : inG ε (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) := LemK.ta_inG_cpart1 ε _
  have h2 : inG ε (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) := LemK.ta_inG_cpart2 ε _
  have hs : Formalism.REAL.cpart1 ε (Matrix.single a b 1) + Complex.I • Formalism.REAL.cpart2 ε (Matrix.single a b 1) =
      Matrix.single a b 1 := LemK.ta_cpart_sum ε _
  show Formalism.REAL.RdV (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) F g +
    Complex.I • Formalism.REAL.RdV (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) F g = _
  rw [rdV_opC hσ hD ι hF hg h1, rdV_opC hσ hD ι hF hg h2, ← opC_smul, ← opC_add, ← smul_mul_assoc,
    ← add_mul, ← SmDerA.actM_smul, ← SmDerA.actM_add, hs, SmDerA.actM_single]

lemma top_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (u : ℂ) (a b : Fin n) :
    Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV ε) u a b F g = opC σ ι g (Capelli.capEntry E u a b * B) := by
  unfold Formalism.QuantumDeterminants.Top Capelli.capEntry
  rw [eabV_opC hσ hD ι hF hg, hF g hg, add_mul, opC_add]
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, opC_smul, add_comm]
  · rw [zero_mul, opC_zero, zero_add, add_zero]

lemma foldr_opC (l : List (ℂ × Fin n × Fin n)) :
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (B : Module.End ℂ D),
      (∀ h, inUJ ε h → F h = opC σ ι h B) → ∀ g, inUJ ε g →
      (l.map fun p => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV ε) p.1 p.2.1 p.2.2).foldr (fun T f => T f) F g =
        opC σ ι g ((l.map fun p => Capelli.capEntry E p.1 p.2.1 p.2.2).prod * B) := by
  induction l with
  | nil =>
    intro F B hF g hg
    simp [hF g hg]
  | cons p l ih =>
    intro F B hF g hg
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    rw [top_opC hσ hD ι (B := (l.map fun p => Capelli.capEntry E p.1 p.2.1 p.2.2).prod * B)
      (fun h hh => ih F B hF h hh) hg, mul_assoc]

lemma qdet_opC {F : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {B : Module.End ℂ D}
    (hF : ∀ h, inUJ ε h → F h = opC σ ι h B) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (u : ℂ) :
    Formalism.QuantumDeterminants.qdetOp (Formalism.REAL.EabV ε) u F g = opC σ ι g (Capelli.capelliC E u * B) := by
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp Capelli.capelliC Capelli.cminor
  rw [Finset.sum_apply, Finset.sum_mul]
  change _ = opL σ ι g _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_mul_assoc, ← Int.cast_smul_eq_zsmul ℂ, map_smul]
  congr 1
  have e1 : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV (E := W →L[ℂ] W) ε) (u - ((k : ℕ) : ℂ)) (id (s k)) (id k)) =
      (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), s k, k)).map
        fun p => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV (E := W →L[ℂ] W) ε) p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun j : Fin n => Capelli.capEntry E (u - ((j : ℕ) : ℂ)) (id (s j)) (id j)) =
      (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), s k, k)).map
        fun p => Capelli.capEntry E p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  rw [e1, e2]
  exact foldr_opC hσ hD ι _ F B hF g hg

end Deriv

end ReciprocityTheory.ChartRestriction.DS.Lap.CapelliClosureMembership
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CayleyConjInvMemHermitianGroup
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem conj_inv_mul_conj {m : ℕ} (P Y g : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) :
    P * ((P⁻¹ * Y * P)⁻¹ * g) * P⁻¹ = Y⁻¹ * (P * g * P⁻¹) := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem unitary_hermitian_form_mul_mem {k r : ℕ} {s x : Mat k r} (hs : s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : s * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = Formalism.QuantumDeterminants.Hpk k r
  have hs' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hs
  have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
  calc (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = xᴴ * (sᴴ * Formalism.QuantumDeterminants.Hpk k r * s) * x := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hs', hx']

theorem conjTranspose_inv_mul_conjTranspose {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : IsUnit P.det) : P⁻¹ᴴ * Pᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv P hP, Matrix.conjTranspose_one]

theorem cayley_conj_mem_unitary_group {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hJ : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show inUJ ε (P * g * P⁻¹)
  rw [← mir_inUJ_iff]
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  have e1 := conjTranspose_inv_mul_conjTranspose P hd
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = P⁻¹ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P⁻¹ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hJ, hg']
    _ = (P⁻¹ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem cayley_conj_inv_mem_hermitian_group {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {Y : Mat k r} (hY : Y ∈ UJset ε) : P⁻¹ * Y * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hJ : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hY' : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε := (mir_inUJ_iff ε Y).2 hY
  show (P⁻¹ * Y * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * Y * P) = Formalism.QuantumDeterminants.Hpk k r
  have e1 := conjTranspose_inv_mul_conjTranspose P hd
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  rw [← hJ]
  calc (P⁻¹ * Y * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * (P⁻¹ * Y * P)
      = Pᴴ * (Yᴴ * ((P⁻¹ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹)) * Y) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Formalism.REAL.Jm ε * P := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one, hY']

theorem ae_mem_unitary_nilpotent_product {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  haveI : SigmaFinite μN := hN.1
  rw [ae_iff]
  have hsub : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r |
      ¬(Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r)} ⊆
      ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) ∪
        (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) := by
    intro p hp
    simp only [Set.mem_ofPred_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, trivial⟩
    · exact Or.inr ⟨trivial, hp⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  · rw [Measure.prod_prod, hN.2.2.1, mul_zero]

theorem finB_frob_eq {k r : ℕ} (g : Mat k r) : frob g = Formalism.FourierDecayAlt.B.gN g := by
  unfold frob Formalism.FourierDecayAlt.B.gN
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem finB_Jct {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem finB_inv_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    g⁻¹ = Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (mir_inUJ_iff ε g).2 hg
  apply Matrix.inv_eq_left_inv
  calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, signature_matrix_sq]

theorem finB_mul_inv {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (mir_inUJ_iff ε g).2 hg
  have h1 : g⁻¹ * g = 1 := by
    rw [finB_inv_eq hg]
    calc Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, signature_matrix_sq]
  exact mul_eq_one_comm.mp h1

theorem finB_frob_inv {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    frob g⁻¹ = frob g := by
  have hJ : (Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = 1 := by rw [finB_Jct, signature_matrix_sq]
  rw [finB_frob_eq, finB_frob_eq, finB_inv_eq hg, S0.DecA.gN_right _ hJ, S0.DecA.gN_left _ hJ, S0.DecA.gN_conjT]

theorem finB_frob_mul_le {k r : ℕ} (a b : Mat k r) : frob (a * b) ≤ frob a * frob b := by
  rw [finB_frob_eq, finB_frob_eq, finB_frob_eq]
  exact S0.DecA.gN_mul_le' a b

theorem finB_one_le {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {g : Mat k r} (hg : g ∈ UJset ε) :
    1 ≤ frob g := by
  have h0 : (1 : ℝ) ≤ frob (1 : Mat k r) := by
    rw [finB_frob_eq]
    have := S0.DecA.gN_entry (1 : Mat k r) ⟨0, by omega⟩ ⟨0, by omega⟩
    simpa using this
  have h1 : frob (1 : Mat k r) ≤ frob g * frob g := by
    have := finB_frob_mul_le g g⁻¹
    rwa [finB_mul_inv hg, finB_frob_inv hg] at this
  nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, ‖g i j‖ ^ 2), show frob g = Real.sqrt (∑ i, ∑ j, ‖g i j‖ ^ 2) from rfl]

theorem finB_le_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Y : Mat k r} (hY : Y ∈ UJset ε) (g : Mat k r) :
    frob g ≤ frob Y * frob (Y⁻¹ * g) := by
  have := finB_frob_mul_le Y (Y⁻¹ * g)
  rwa [← Matrix.mul_assoc, finB_mul_inv hY, Matrix.one_mul] at this

theorem finB_intJ {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (hq : 1 ≤ S7.q0 ε) (b : ℝ)
    (hb : 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < b) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε) := by
  refine integrable_muG_of_haar ε (fun g => frob g ^ (-b)) (fun ν _ => ?_)
  obtain ⟨s, hs⟩ := S7.exists_signVG ε
  have hb0 : 0 ≤ b := by
    have : (0 : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    linarith
  have hmem : ∀ g : S7.UJ ε, S7.toM g ∈ UJset ε := fun g => unitary_matrix_mem_set ε g
  have hone : ∀ g : S7.UJ ε, 1 ≤ frob (S7.toM g) := fun g => finB_one_le (hmem g)
  have hfr : ∀ g : Mat k r, frob g = Real.sqrt (S7.hs g) := fun g => rfl
  have hcont : Continuous (fun g : S7.UJ ε => frob (S7.toM g) ^ (-b)) := by
    have h1 : Continuous (fun g : S7.UJ ε => frob (S7.toM g)) := by
      have : Continuous (fun g : Mat k r => frob g) := by
        simp only [hfr]; exact Real.continuous_sqrt.comp S7.hs_contVG
      exact this.comp (S7.continuous_toM ε)
    exact h1.rpow_const (fun g => Or.inl (by linarith [hone g]))
  refine S7.integrable_of_decayVG ε s ν _ hcont.aestronglyMeasurable 1 (fun g _ => ?_) b ?_ (fun g hg => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hone g]) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hone g) (by linarith)
  · rw [hs]; push_cast at hb ⊢; linarith
  · set H := S7.hs (S7.toM g) with hH
    have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have hn0 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := by linarith
    have hH0 : 0 < H := by
      have : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) * Real.exp 2 + 1 := by positivity
      linarith
    have hq0 : 0 < H / ((2 * r + k + 1 : ℕ) : ℝ) := div_pos hH0 hn0
    refine ⟨Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2, ?_, ?_⟩
    · rw [show 2 * (Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2) = Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) by ring,
        Real.exp_log hq0, mul_div_cancel₀ _ hn0.ne']
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hone g]) _), one_mul, hfr,
        ← hH, Real.sqrt_eq_rpow, ← Real.rpow_mul hH0.le]
      have e : -(b * (Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) / 2)) =
          Real.log (H / ((2 * r + k + 1 : ℕ) : ℝ)) * (-(b / 2)) := by ring
      rw [e, ← Real.rpow_def_of_pos hq0, Real.div_rpow hH0.le hn0.le, show (1 / 2 : ℝ) * -b = -(b / 2) by ring]
      have h1 : (1 : ℝ) ≤ (((2 * r + k + 1 : ℕ) : ℝ) ^ (-(b / 2)))⁻¹ := by
        rw [Real.rpow_neg hn0.le, inv_inv]
        exact Real.one_le_rpow hn (by linarith)
      rw [div_eq_mul_inv]
      have h2 : 0 ≤ H ^ (-(b / 2)) := Real.rpow_nonneg hH0.le _
      exact le_mul_of_one_le_right h2 h1

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem gapNeed : GapNeedStatement := by
  intro k r ε h hp hq hg
  unfold StepGap at hg
  unfold hNeed S7.q0
  obtain ⟨h1, h2⟩ := hg
  rw [← Nat.cast_min] at h2 ⊢
  have hqr : ((qOf ε : ℕ) : ℝ) - 1 = (r : ℝ) := by rw [hq]; push_cast; ring
  rw [hqr]
  have hm : 1 ≤ min (pOf ε) (qOf ε) := by
    by_contra hc
    have h0 : min (pOf ε) (qOf ε) = 0 := by omega
    rw [h0] at h2
    simp at h2
    linarith [le_max_left (0 : ℝ) (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2)]
  refine ⟨hm, ?_⟩
  set m := min (pOf ε) (qOf ε) with hmdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; norm_cast; omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : 1 ≤ Real.sqrt (2 * (m : ℝ)) := Real.one_le_sqrt.mpr (by linarith)
  set s := 8 * Real.sqrt (2 * (m : ℝ)) with hs
  have hs8 : 8 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  set X := max (2 * N * (m : ℝ)) (2 * (r : ℝ) * N ^ 2) with hX
  have hX1 : 2 * N * m ≤ X := le_max_left _ _
  have hNm : 1 ≤ N * m := by nlinarith
  have hC : s * (4 * X + 1) < h := by
    have h4 := h2
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hspos] at h4
    linarith
  have hsX : 8 * X ≤ s * X := by nlinarith
  refine max_lt (by linarith) (max_lt ?_ hC)
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end

