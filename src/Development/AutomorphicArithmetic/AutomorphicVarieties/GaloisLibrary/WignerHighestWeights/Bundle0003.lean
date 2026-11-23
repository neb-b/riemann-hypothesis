module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]


omit [Algebra ℂ A] in
private noncomputable def sL (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) : Cinf E →ₗ[ℝ] A where
  toFun x := L (toL (Matrix.single i j x))
  map_add' x y := by
    have h : toL (Matrix.single i j (x + y)) = toL (Matrix.single i j x) + toL (Matrix.single i j y) :=
      congrArg toL (Matrix.single_add i j x y)
    exact (congrArg L h).trans (L.map_add _ _)
  map_smul' c x := by
    have h : toL (Matrix.single i j (c • x)) = c • toL (Matrix.single i j x) :=
      congrArg toL (Matrix.smul_single c i j x).symm
    exact (congrArg L h).trans (L.map_smul _ _)

omit [Algebra ℂ A] in
private theorem sL_apply (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) (x : Cinf E) :
    sL L i j x = L (toL (Matrix.single i j x)) := rfl

omit [Algebra ℂ A] in
private theorem sL_comm (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (i j k l : Fin a) (x y : Cinf E) :
    sL L i j x * sL L k l y - sL L k l y * sL L i j x =
      (if j = k then sL L i l (x * y) else 0) - (if l = i then sL L k j (x * y) else 0) := by
  have h := hL (Matrix.single i j x) (Matrix.single k l y)
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  rw [e, map_sub] at h
  simp only [sL_apply]
  rw [h]
  have z : L (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]

private theorem eL_comm_aux (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    eL L τ i j * eL L τ' k l - eL L τ' k l * eL L τ i j =
      (if j = k then (1 / 4 : ℂ) • (sL L i l (atEmb τ 1 * atEmb τ' 1) - sL L i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L i l (atEmb τ 1 * atEmb τ' .I) + sL L i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (sL L k j (atEmb τ 1 * atEmb τ' 1) - sL L k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L k j (atEmb τ 1 * atEmb τ' .I) + sL L k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [eL, ← sL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

end

end UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL in
theorem UpperTheory.V.AlgRepEndIrreducible.eLRel :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Module ℝ A] [IsScalarTower ℝ ℂ A] (L : Lie E a →ₗ[ℝ] A),
      IsLieHom L → IsMultiGl (eL L) := by
  intro E _ _ _ a A _ _ _ _ L hL
  refine ⟨fun τ i j k l => ?_, fun τ τ' h i j k l => ?_⟩
  · have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by
      rw [atEmb_eq]; simp
    rw [eL_comm_aux L hL]
    simp only [atEmb_mul, one_mul, mul_one, e, map_neg, eL, ← sL_apply]
    congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)
  · rw [← sub_eq_zero, eL_comm_aux L hL]
    by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
    · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
        rw [atEmb_eq]; simp
      have e' : atEmb τ (-1) = -atEmb τ 1 := by
        rw [atEmb_eq]; simp
      simp [atEmb_conj, atEmb_mul, e, e']
    · simp [atEmb_mul_of_ne hw]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelDer
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpDer {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (D : Module.End ℂ M) (g : X → X) (n : ℕ) :
    ∀ (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, D * b i y - b i y * D = b i (g y)) → ∀ x : Fin n → X,
      D * rp n b x = rp n b x * D + ∑ k, rp n b (Function.update x k (g (x k))) := by
  induction n with
  | zero => intro b _ x; simp [rp_zero]
  | succ n ih =>
    intro b hb x
    have h1 := ih (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : D * b 0 (x 0) = b 0 (x 0) * D + b 0 (g (x 0)) := by rw [← hb]; abel
    rw [Fin.sum_univ_succ]
    simp only [rp_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← mul_assoc, h1, add_mul, mul_assoc, h0, Finset.sum_mul, mul_add, mul_assoc, add_assoc]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telDer :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (D : Module.End ℂ M) (g : X → X),
      (∀ i y, D * a i y - a i y * D = a i (g y)) → (∀ i y, D * b i y - b i y * D = b i (g y)) →
      ∀ f f' : X →ₗ[ℂ] M, (∀ y, D (f y) = f' y + f (g y)) → ∀ x : Fin n → X,
        D (tel n a b f x) = tel n a b f' x + ∑ k, tel n a b f (Function.update x k (g (x k))) := by
  intro X M _ _ _ _ n
  induction n with
  | zero => intro a b D g _ _ f f' _ x; simp [tel_zero]
  | succ n ih =>
    intro a b D g ha hb f f' hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) D g (fun i y => ha i.succ y) (fun i y => hb i.succ y) f f' hf (Fin.tail x)
    have h2 := rpDer D g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : ∀ m, D (a 0 (x 0) m) = a 0 (x 0) (D m) + a 0 (g (x 0)) m := by
      intro m
      rw [← ha]
      simp
    have h3 : ∀ m, D (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (D m) +
        ∑ k : Fin n, rp n (Fin.tail b) (Function.update (Fin.tail x) k (g (x k.succ))) m := by
      intro m
      have := LinearMap.congr_fun h2 m
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply] at this
      exact this
    have h4 : D (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) = tel n (Fin.tail a) (Fin.tail b) f' (Fin.tail x) +
        ∑ k : Fin n, tel n (Fin.tail a) (Fin.tail b) f (Function.update (Fin.tail x) k (g (x k.succ))) := h1
    rw [Fin.sum_univ_succ]
    simp only [tel_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), h0, h3, h4, hf, map_add (f := _), map_add (f := _), map_sum, Finset.sum_add_distrib]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelML
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rpML {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) :
    ∃ R : (Fin n → X) →ₘₗ[ℂ] Module.End ℂ M, ∀ x, R x = rp n b x := by
  induction n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) _ 1, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih (Fin.tail b)
    let g : X →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] Module.End ℂ M :=
      { toFun := fun x0 => (LinearMap.mulRight ℂ (b 0 x0)).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp [mul_add]
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    refine ⟨LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => X) g, fun x => ?_⟩
    rw [rp_succ, ← hR]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telML :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      ∃ T : (X →ₗ[ℂ] M) →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] M, ∀ f x, T f x = tel n a b f x := by
  intro X M _ _ _ _ n a b
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih (Fin.tail a) (Fin.tail b)
    obtain ⟨R, hR⟩ := rpML n (Fin.tail b)
    let g : (X →ₗ[ℂ] M) → X →ₗ[ℂ] (Fin n → X) →ₘₗ[ℂ] M := fun f =>
      { toFun := fun x0 => (a 0 x0).compMultilinearMap (T f) +
          (LinearMap.applyₗ (f x0) : Module.End ℂ M →ₗ[ℂ] M).compMultilinearMap R
        map_add' := fun u v => MultilinearMap.ext fun y => by simp; abel
        map_smul' := fun c u => MultilinearMap.ext fun y => by simp }
    have hg : ∀ (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X),
        LinearMap.uncurryLeft (σ := RingHom.id ℂ) (M := fun _ : Fin (n + 1) => X) (g f) x =
        a 0 (x 0) (T f (Fin.tail x)) + R (Fin.tail x) (f (x 0)) := by
      intro f x
      rfl
    refine ⟨{ toFun := fun f => LinearMap.uncurryLeft (M := fun _ : Fin (n + 1) => X) (g f)
              map_add' := fun u v => MultilinearMap.ext fun y => ?_
              map_smul' := fun c u => MultilinearMap.ext fun y => ?_ }, fun f x => ?_⟩
    · simp only [add_apply, hg, map_add (f := _), LinearMap.add_apply]
      abel
    · simp only [smul_apply, hg, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add]
    · rw [tel_succ, ← hT, ← hR]
      exact hg f x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelSum
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem UpperTheory.V.AlgRepEndIrreducible.telSum_commute_rp {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) : ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ j y, Commute T (b j y)) →
      ∀ x : Fin n → X, Commute T (rp n b x) := by
  intro n
  induction n with
  | zero => intro b _ x; rw [rp_zero]; exact Commute.one_right T
  | succ n ih =>
    intro b h x
    rw [rp_succ]
    exact (ih (Fin.tail b) (fun j y => h j.succ y) (Fin.tail x)).mul_right (h 0 (x 0))

theorem UpperTheory.V.AlgRepEndIrreducible.telSum :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M),
      (∀ i j x y, Commute (a i x) (b j y)) → ∀ (m : M) (f : X →ₗ[ℂ] M), (∀ i y, f y = a i y m - b i y m) →
      ∀ x : Fin n → X, tel n a b f x = (List.ofFn fun i => a i (x i)).prod m - rp n b x m := by
  intro X M _ _ _ _ n
  induction n with
  | zero =>
    intro a b _ m f _ x
    rw [tel_zero, rp_zero]
    simp
  | succ n ih =>
    intro a b hc m f hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) (fun i j u v => hc i.succ j.succ u v) m f (fun i y => hf i.succ y)
      (Fin.tail x)
    have h2 : Commute (a 0 (x 0)) (rp n (Fin.tail b) (Fin.tail x)) :=
      UpperTheory.V.AlgRepEndIrreducible.telSum_commute_rp _ n _ (fun j y => hc 0 j.succ (x 0) y) _
    have h3 : a 0 (x 0) (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (a 0 (x 0) m) :=
      LinearMap.congr_fun h2.eq m
    rw [tel_succ, rp_succ, h1, hf 0 (x 0), List.ofFn_succ, List.prod_cons, map_sub, map_sub, h3,
      Module.End.mul_apply, Module.End.mul_apply]
    simp only [Fin.tail]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TensDer
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.tensDer :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), SepDer (tensorK π Ξ) (tensorLie π Ξ) := by
  intro E _ _ _ a π Ξ k Z h0 hk m' hm
  let e := TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d)
  have h1 : e m' ≠ 0 := fun h => hm (e.map_eq_zero_iff.1 h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
  have h2 : (e m' j).1.1 ≠ 0 := fun h => hj (Subtype.ext (Subtype.ext h))
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : π.V ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (e m j).1.1 g
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : π.V) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1.1 g * v j := fun φ v => by
    have h : e (φ ⊗ₜ v) j = v j • φ := by
      simp only [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    change (e (φ ⊗ₜ v) j).1.1 g = _
    rw [h, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    simp only [tensorK, tensorLie_tmul, TensorProduct.map_tmul, map_add (f := _), hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5
end

