module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MemSEOfFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsotropicSplittingOfTwoMulLe
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
noncomputable section
private theorem core_pk {A : Type} [CommRing A] (S : Subring A) (s : A →+* A) (hS : ∀ x ∈ S, s x ∈ S)
    (ss : ∀ x, s (s x) = x) {e : A} (he : e ∈ S) (h1 : e + s e = 1) (h2 : e * s e = 0) {n d : ℕ} (hnd : 2 * n ≤ d)
    {Γ G' : Matrix (Fin d) (Fin d) A} (hΓ : ∀ i j, Γ i j ∈ S) (hG' : ∀ i j, G' i j ∈ S) (hi : G' * Γ = 1)
    (hsk : (Γ.map s)ᵀ = -Γ) :
    ∃ (c : Matrix (Fin n) (Fin d) A) (ρ : Matrix (Fin d) (Fin n) A), (∀ i j, c i j ∈ S) ∧ (∀ i j, ρ i j ∈ S) ∧
      c * ρ = 1 ∧ c * Γ * (c.map s)ᵀ = 0 := by
  classical
  let f₁ : Fin n → Fin d := fun i => ⟨i, by omega⟩
  let f₂ : Fin n → Fin d := fun i => ⟨i + n, by omega⟩
  have i₁ : Function.Injective f₁ := fun a b h => Fin.ext (by simpa [f₁] using h)
  have i₂ : Function.Injective f₂ := fun a b h => Fin.ext (by simpa [f₂] using h)
  have dj : ∀ a b, f₁ a ≠ f₂ b := fun a b h => by
    have := congrArg Fin.val h
    simp only [f₁, f₂] at this
    omega
  have key : ∀ f g : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f)ᵀ * (1 : Matrix (Fin d) (Fin d) A).submatrix id g =
      (1 : Matrix (Fin d) (Fin d) A).submatrix f g := fun f g => by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul]
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ = (1 : Matrix (Fin d) (Fin d) A).submatrix id f₁ := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E₂, E₂ = (1 : Matrix (Fin d) (Fin d) A).submatrix id f₂ := ⟨_, rfl⟩
  have p11 : E₁ᵀ * E₁ = 1 := by rw [hE₁, key, Matrix.submatrix_one _ i₁]
  have p22 : E₂ᵀ * E₂ = 1 := by rw [hE₂, key, Matrix.submatrix_one _ i₂]
  have p12 : E₁ᵀ * E₂ = 0 := by
    rw [hE₁, hE₂, key]
    exact Matrix.ext fun a b => Matrix.one_apply_ne (dj a b)
  have p21 : E₂ᵀ * E₁ = 0 := by
    rw [hE₁, hE₂, key]
    exact Matrix.ext fun a b => Matrix.one_apply_ne (dj b a).symm
  have intE : ∀ f : Fin n → Fin d, ∀ i j, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f) i j ∈ S := fun f i j => by
    simp only [Matrix.submatrix_apply, id, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have mapE : ∀ f : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f).map s = (1 : Matrix (Fin d) (Fin d) A).submatrix id f :=
    fun f => Matrix.ext fun i j => by
      simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
      split_ifs <;> simp
  have hΓG : Γ * G' = 1 := mul_eq_one_comm.1 hi
  obtain ⟨T, hT⟩ : ∃ T, T = (G'.map s)ᵀ := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (Γ.map s)ᵀ := ⟨_, rfl⟩
  have hTQ : T * Q = 1 := by
    rw [hT, hQ, ← Matrix.transpose_mul, ← Matrix.map_mul, hΓG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hTΓ : T * Γ = -1 := by
    rw [← neg_neg (T * Γ), ← Matrix.mul_neg, ← hsk, ← hQ, hTQ]
  have mapT : T.map s = G'ᵀ := Matrix.ext fun i j => by simp [hT, ss]
  have he2 : e * e = e := by
    have : e * (e + s e) = e := by rw [h1, mul_one]
    rwa [mul_add, h2, add_zero] at this
  have hs2 : s e * s e = s e := by
    have : s e * (e + s e) = s e := by rw [h1, mul_one]
    rwa [mul_add, mul_comm, h2, zero_add] at this
  have h2' : s e * e = 0 := by rw [mul_comm, h2]
  have hsS : s e ∈ S := hS _ he
  have iE₁ : ∀ i j, E₁ i j ∈ S := fun i j => hE₁ ▸ intE f₁ i j
  have iE₂ : ∀ i j, E₂ i j ∈ S := fun i j => hE₂ ▸ intE f₂ i j
  have iT : ∀ i j, T i j ∈ S := fun i j => by rw [hT]; exact hS _ (hG' j i)
  have iQ : ∀ i j, Q i j ∈ S := fun i j => by rw [hQ]; exact hS _ (hΓ j i)
  refine ⟨e • E₁ᵀ + s e • (E₂ᵀ * T), e • E₁ + s e • (Q * E₂), fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem he (iE₁ j i)) (mul_mem hsS (by rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (iE₂ k i) (iT k j)))
  · rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem he (iE₁ i j)) (mul_mem hsS (by rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (iQ i k) (iE₂ k j)))
  · have x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * (e • E₁ + s e • (Q * E₂)) = (e * e) • (E₁ᵀ * E₁) + (s e * e) • (E₁ᵀ * (Q * E₂)) +
        (e * s e) • (E₂ᵀ * T * E₁) + (s e * s e) • (E₂ᵀ * T * (Q * E₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      abel
    have x2 : E₂ᵀ * T * (Q * E₂) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, hTQ, Matrix.one_mul, p22]
    rw [x1, he2, hs2, h2, h2', p11, x2, zero_smul, zero_smul, add_zero, add_zero, ← add_smul, h1, one_smul]
  · have mapE₁ : E₁ᵀ.map s = E₁ᵀ := by rw [Matrix.transpose_map, hE₁, mapE]
    have mapE₂ : E₂ᵀ.map s = E₂ᵀ := by rw [Matrix.transpose_map, hE₂, mapE]
    have e3 : (E₂ᵀ * T).map s = E₂ᵀ * G'ᵀ := by rw [Matrix.map_mul, mapT, mapE₂]
    have hcm : (e • E₁ᵀ + s e • (E₂ᵀ * T)).map s = s e • E₁ᵀ + e • (E₂ᵀ * G'ᵀ) := Matrix.ext fun i j => by
      have a1 := congrFun (congrFun mapE₁ i) j
      have a2 := congrFun (congrFun e3 i) j
      simp only [Matrix.map_apply] at a1 a2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, ss, a1, a2]
    rw [hcm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    have x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * Γ * (s e • E₁ + e • (G' * E₂)) = (s e * e) • (E₁ᵀ * Γ * E₁) + (e * e) • (E₁ᵀ * Γ * (G' * E₂)) +
        (s e * s e) • (E₂ᵀ * T * Γ * E₁) + (e * s e) • (E₂ᵀ * T * Γ * (G' * E₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      abel
    have x2 : E₁ᵀ * Γ * (G' * E₂) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ, hΓG, Matrix.one_mul, p12]
    have x3 : E₂ᵀ * T * Γ * E₁ = 0 := by
      rw [Matrix.mul_assoc E₂ᵀ, hTΓ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, p21, neg_zero]
    rw [x1, x2, x3, h2, h2', zero_smul, zero_smul, smul_zero, smul_zero, add_zero, add_zero, add_zero]
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
private theorem sig_sig_pk (h : ∀ x, σ (σ x) = x) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
private theorem ext_at_pk {ι κ : Type} {M M' : Matrix ι κ (AE F E)} (h : At (evFin F v) M) (h' : At (evFin F v) M')
    (e : M.map (compFin F E v) = M'.map (compFin F E v)) : M = M' :=
  Matrix.ext fun i j => sub_eq_zero.1 (PositivityTheory.ThKH.Iwas.eq_zero_of_at (v := v)
    (fun u hu => congrFun (congrFun (PositivityTheory.ThKH.Iwas.at_sub h h' u hu) i) j)
    (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e i) j))
private theorem sgE_mem_Oh_pk {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : PositivityTheory.ThKH.Iwas.sgE E v y ∈ Oh E v := by
  refine intLoc_induction (p := fun y => PositivityTheory.ThKH.Iwas.sgE E v y ∈ Oh E v) (fun a ha x => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · refine AddSubgroup.subset_closure ⟨PositivityTheory.ThKH.Iwas.sg v a, PositivityTheory.ThKH.Iwas.at_sg a, by rwa [PositivityTheory.ThKH.Iwas.ev_sg], x, ?_⟩
    change (PositivityTheory.ThKH.Iwas.sg v a) ⊗ₜ[F] (x : E) = (PositivityTheory.ThKH.Iwas.sg v a * 1) ⊗ₜ[F] (x : E)
    rw [mul_one]
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem hy hz
  · rw [map_neg]; exact neg_mem hy
private theorem mem_Oh_pk {x : AE F E} (hx : At (evFin F v) x) (h : compFin F E v x ∈ intLoc F E v) : x ∈ Oh E v := by
  have h1 := hx (1 - PositivityTheory.ThKH.Iwas.sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])
  rw [sub_smul, one_smul, ← PositivityTheory.ThKH.Iwas.sgE_comp, sub_eq_zero] at h1
  rw [h1]
  exact sgE_mem_Oh_pk h
private theorem at_sgEM_pk {ι κ : Type} (M : Matrix ι κ (Fv F v ⊗[F] E)) : At (evFin F v) (M.map (PositivityTheory.ThKH.Iwas.sgE E v)) :=
  fun u hu => Matrix.ext fun i j => PositivityTheory.ThKH.Iwas.at_sgE _ u hu
private theorem comp_sgEM_pk {ι κ : Type} (M : Matrix ι κ (Fv F v ⊗[F] E)) :
    (M.map (PositivityTheory.ThKH.Iwas.sgE E v)).map (compFin F E v) = M :=
  Matrix.ext fun i j => PositivityTheory.ThKH.Iwas.comp_sgE _
end
theorem UpperTheory.exists_isotropic_splitting_of_two_mul_le :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (W : Spc F E d) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → W.IsSkew σ B r s → 2 * n ≤ d → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  intro F E _ _ _ _ _ σ B n d W r s hB hW hnd v t
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  obtain ⟨a, g, l, ha, hal, hΓ, G', hG', hi⟩ :=
    _root_.GlobalTheory.ThK.Dbl.Frame.exists_loc_k hB (Or.inr hW) (PositivityTheory.ThKH.Iwas.det_ne_zero hW) v
  let ι := inclR (F := F) (E := E) (Fv F v)
  let c' := sigR (Fv F v) σ
  have mJ : ((W.J.map ι).map c')ᵀ = -W.J.map ι := Matrix.ext fun i j => by
    change c' (ι (W.J j i)) = -ι (W.J i j)
    rw [show c' (ι (W.J j i)) = ι (σ (W.J j i)) from rfl, hW.skew i j, map_neg]
  have mg : (g.1.map c').map c' = g.1 := Matrix.ext fun i j => sig_sig_pk hσ _
  have sk : ((g.1ᵀ * W.J.map ι * g.1.map c').map c')ᵀ = -(g.1ᵀ * W.J.map ι * g.1.map c') := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, mg, mJ, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have idem := splitIdem_mul_self hc t
  have sI := sigR_splitIdem hc t
  obtain ⟨c, ρ, ic, iρ, hcρ, hgr⟩ := core_pk (intLoc F E v) c' (fun x hx => sigR_mem_intLoc σ hx) (sig_sig_pk hσ)
    (splitIdem_mem hc t) (by change _ + sigR _ σ _ = 1; rw [sI]; ring)
    (by change _ * sigR _ σ _ = 0; rw [sI, mul_sub, mul_one, idem, sub_self]) hnd hΓ hG' hi sk
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = c * a.1ᵀ := ⟨_, rfl⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = (a⁻¹).1ᵀ * ρ := ⟨_, rfl⟩
  refine ⟨Y₀.map (PositivityTheory.ThKH.Iwas.sgE E v), R₀.map (PositivityTheory.ThKH.Iwas.sgE E v), ⟨fun i => ?_, ?_, ?_, fun z hz j => ?_⟩⟩
  · refine (PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W _).2 ⟨fun u hu => funext fun j => PositivityTheory.ThKH.Iwas.at_sgE _ u hu, ?_⟩
    have h1 := (ha (c i)).1 (ic i)
    convert h1 using 1
    funext j
    change compFin F E v (PositivityTheory.ThKH.Iwas.sgE E v (Y₀ i j)) = _
    rw [PositivityTheory.ThKH.Iwas.comp_sgE, hY₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, mul_comm]
  · have atE : At (evFin F v) (eM v n : Matrix (Fin n) (Fin n) (AE F E)) := fun u hu => by
      rw [smul_smul, show u * PositivityTheory.ThKH.Iwas.sg v 1 = 0 from PositivityTheory.ThKH.Iwas.at_sg 1 u hu, zero_smul]
    refine ext_at_pk (PositivityTheory.ThKH.Iwas.at_mul_left (at_sgEM_pk _) _) atE ?_
    have e1 : (eM v n : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) = 1 := Matrix.ext fun i j => by
      change compFin F E v (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _
      rw [← PositivityTheory.ThKH.Iwas.sgE_comp, PositivityTheory.ThKH.Iwas.comp_sgE, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [Matrix.map_mul, comp_sgEM_pk, comp_sgEM_pk, e1, hY₀, hR₀, Matrix.mul_assoc, ← Matrix.mul_assoc a.1ᵀ, ← Matrix.transpose_mul,
      Units.inv_mul, Matrix.transpose_one, Matrix.one_mul, hcρ]
  · refine ext_at_pk (PositivityTheory.ThKH.Iwas.at_mul_left (PositivityTheory.ThKH.Iwas.at_mul_left (at_sgEM_pk _) _) _) PositivityTheory.ThKH.Iwas.at_zero ?_
    have e1 : (incM F W.J).map (compFin F E v) = W.J.map ι :=
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] W.J i k) (map_one (evFin F v))
    have e2 : (((Y₀.map (PositivityTheory.ThKH.Iwas.sgE E v)).map (cA σ))ᵀ).map (compFin F E v) = (Y₀.map c')ᵀ := Matrix.ext fun i j => by
      change compFin F E v (cA σ (PositivityTheory.ThKH.Iwas.sgE E v (Y₀ j i))) = c' (Y₀ j i)
      rw [GlobalTheory.ThK.Dbl.Vf2.comp_cA, PositivityTheory.ThKH.Iwas.comp_sgE]
    have e3 : a.1.map c' = c' l.1 • g.1.map c' := Matrix.ext fun i j => by
      change c' (a.1 i j) = c' l.1 * c' (g.1 i j)
      rw [hal, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [Matrix.map_mul, Matrix.map_mul, comp_sgEM_pk, e1, e2, hY₀, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map,
      Matrix.transpose_transpose, e3, hal]
    have e4 : c * (l.1 • g.1)ᵀ * W.J.map ι * ((c' l.1 • g.1.map c') * (c.map c')ᵀ) =
        (l.1 * c' l.1) • (c * (g.1ᵀ * W.J.map ι * g.1.map c') * (c.map c')ᵀ) := by
      simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      rw [mul_comm]
    rw [e4, hgr, smul_zero, Matrix.map_zero _ (map_zero _)]
  · obtain ⟨z1, z2⟩ := (PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W z).1 hz
    have eT : z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v) = (R₀.map (PositivityTheory.ThKH.Iwas.sgE E v))ᵀ *ᵥ z := (Matrix.mulVec_transpose _ _).symm
    have hat : At (evFin F v) (z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v)) := by
      rw [eT]; exact PositivityTheory.ThKH.Iwas.at_mulVec_right _ z1
    refine mem_Oh_pk (fun u hu => congrFun (hat u hu) j) ?_
    obtain ⟨y, hy⟩ : ∃ y, y = (a⁻¹).1 *ᵥ (compFin F E v ∘ z) := ⟨_, rfl⟩
    have iy := (ha y).2 (by rwa [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
    have e1 : compFin F E v ((z ᵥ* R₀.map (PositivityTheory.ThKH.Iwas.sgE E v)) j) = (y ᵥ* ρ) j := by
      rw [eT, RingHom.map_mulVec, Matrix.transpose_map, comp_sgEM_pk, hR₀, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_transpose]
    rw [e1]
    change ∑ k, y k * ρ k j ∈ _
    exact sum_mem fun k _ => mul_mem (iy k) (iρ k j)
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsVacSplitK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
open GlobalTheory.SplitInvFormF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
open GlobalTheory.SplitInvFormF
theorem exists_vac_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  classical
  have he' := isSplitIdemF_conj he
  let Y := conjHalf σ e nS nT
  let X := conjHalf σ (cAF σ e) nS nT
  obtain ⟨U, hU, hUf⟩ := hf₀.level
  obtain ⟨G, hGX, hGU⟩ := _root_.PositivityTheory.ThKW.exists_finite_open_subgroup_split F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  have hGX' : ∀ g ∈ G, g ∈ X := fun g hg => mem_conjHalf_conj he (hGX g hg)
  let YK : AddSubgroup (WOF F E nS nT) :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1}
      add_mem' := fun {a b} ha hb => ⟨Y.add_mem ha.1 hb.1, fun k hk hkf => by
        rw [commF_add_right, ha.2 k hk hkf, hb.2 k hk hkf, one_mul]⟩
      zero_mem' := ⟨Y.zero_mem, fun k _ _ => commF_zero_right k⟩
      neg_mem' := fun {a} ha => ⟨Y.neg_mem ha.1, fun k hk hkf => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) k a
        rwa [ha.2 k hk hkf, mul_one] at this⟩ }
  let Q : AddSubgroup YK :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hQfix : ∀ q ∈ Q, heisOF σ JS JT ξ₀ B.ψ (q : WOF F E nS nT) f₀ = f₀ := fun q hq =>
    hUf _ (hGU _ q.2.1 hq) (fin_of_mem he q.2.1)
  have hN : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT ξ₀ B.ψ (k • g) f₀ = f₀ := fun g hg => exists_nsmul_fix he' (hGX' g hg) hf₀
  choose! Ng hNg0 hNg using hN
  set N := ∏ g ∈ G, Ng g with hNdef
  have hN0 : 0 < N := Finset.prod_pos fun g hg => hNg0 g hg
  have hpowN : ∀ g ∈ G, ∀ y : YK, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) ^ N = 1 := by
    intro g hg y
    obtain ⟨m, hm⟩ : Ng g ∣ N := Finset.dvd_prod_of_mem _ hg
    rw [← commF_nsmul_left]
    refine y.2.2 _ (nsmul_mem (hGX' g hg) N) ?_
    rw [hm, mul_nsmul]
    exact heisOF_nsmul_fix he' (nsmul_mem (hGX' g hg) _) (hNg g hg) m
  haveI : Finite (YK ⧸ Q) := by
    let S := (Polynomial.nthRoots N (1 : ℂ)).toFinset
    refine Finite.of_injective (β := G → S) (fun a g => ⟨commF σ JS JT ξ₀ B.ψ g (Quotient.out a : YK), ?_⟩) ?_
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN0]
      exact hpowN g g.2 _
    · intro a b hab
      rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq]
      intro g hg
      have h1 := congrArg Subtype.val (congrFun hab ⟨g, hg⟩)
      simp only at h1
      show commF σ JS JT ξ₀ B.ψ g ((-Quotient.out a + Quotient.out b : YK) : WOF F E nS nT) = 1
      rw [AddSubgroup.coe_add, commF_add_right, ← h1, AddSubgroup.coe_neg, commF_neg_right]
  let Ch : Set (YK → ℂ) := {χ | ∃ x ∈ X, (∀ q ∈ Q, commF σ JS JT ξ₀ B.ψ x (q : WOF F E nS nT) = 1) ∧ χ = fun y : YK => commF σ JS JT ξ₀ B.ψ x (y : WOF F E nS nT)}
  obtain ⟨χ, ⟨x, hxX, -, rfl⟩, w, hwspan, hw0, hweig⟩ := exists_eigen_of_sep
    (fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT))
    (fun a b f => heisOF_add_half he a.2.1 b.2.1 f) Q f₀ hf₀0 hQfix Ch
    (by rintro _ ⟨x, -, -, rfl⟩ a b; exact commF_add_right x a b)
    (by rintro _ ⟨x, -, hx, rfl⟩ q hq; exact hx q hq)
    (by
      rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨x', hx', hxQ', rfl⟩
      refine ⟨x + x', X.add_mem hx hx', fun q hq => by rw [commF_add_left, hxQ q hq, hxQ' q hq, one_mul], ?_⟩
      funext y
      simp only [Pi.mul_apply, commF_add_left])
    ⟨0, X.zero_mem, fun q _ => commF_zero_left _, by funext y; simp only [Pi.one_apply, commF_zero_left]⟩
    (fun y hy => by
      have hy' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1 := hy
      push_neg at hy'
      obtain ⟨g, hg, hne⟩ := hy'
      exact ⟨_, ⟨g, hGX' g hg, fun q hq => hq g hg, rfl⟩, hne⟩)
  have hspan_theta : Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    exact _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hf₀)
  have hspan_fix : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      LinearMap.eqLocus (heisL σ JS JT ξ₀ B.ψ k) LinearMap.id := fun k hk hkf => Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    show heisOF σ JS JT ξ₀ B.ψ k (heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) = heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀
    rw [heisOF_comm, y.2.2 k hk hkf, one_smul, hkf])
  have hwθ : IsThetaFunOF σ JS JT ξ₀ B.ψ w := hspan_theta hwspan
  refine ⟨heisOF σ JS JT ξ₀ B.ψ (-x) w, _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hwθ, ?_, ?_⟩
  · intro h0
    apply hw0
    have := heisOF_add_half (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) he' hxX (X.neg_mem hxX) w
    rw [add_neg_cancel, heisOF_zero] at this
    rw [this, show heisOF σ JS JT ξ₀ B.ψ (-x) w = 0 from h0]
    exact map_zero (heisL σ JS JT ξ₀ B.ψ x)
  · intro y hy
    by_cases hyK : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1
    · left
      have hyy : y ∈ YK := ⟨hy, hyK⟩
      have h1 := hweig ⟨y, hyy⟩
      change commF σ JS JT ξ₀ B.ψ x y • heisOF σ JS JT ξ₀ B.ψ y w = w at h1
      rw [heisOF_comm, commF_swap]
      conv_rhs => rw [← h1]
      exact (GlobalTheory.WeilPartsF.heisOF_smul _ _ _).symm
    · right
      push_neg at hyK
      obtain ⟨k, hk, hkf, hne⟩ := hyK
      refine ⟨k, ?_, hne⟩
      rw [heisOF_comm, commF_half he' hk (X.neg_mem hxX), one_smul]
      congr 1
      exact hspan_fix k hk hkf hwspan
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LintegralSqOmK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
noncomputable section
namespace GlobalTheory.FinLatUnitF
open GlobalTheory.FinLatF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
theorem lintegral_sq_Om_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ hc Λ w lam Om h μ 𝓕 hμ h𝓕 p f
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hB.cm
  have hn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  obtain ⟨Bf, hB1, hB2⟩ := _root_.GlobalTheory.T.theta_subspace_haar_integral F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ
    (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB2, hB2, GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opFF hσ hS hT hξ hc h.hw) (fun x y => hn _) lam h.good _ h.sd h.span
    (rhoFF σ JS JT p) (gamFF_rhoFF hS ξ₀ B.ψ p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) Bf]
  intro x u v
  have h1 : ∀ u : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, opFF hc w x u =
      phaseF σ JS JT ξ₀ B.ψ w x • (⟨heisOF σ JS JT ξ₀ B.ψ x u, hc x u u.2⟩ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) :=
    fun u => rfl
  have h2 : phaseF σ JS JT ξ₀ B.ψ w x * (starRingEnd ℂ) (phaseF σ JS JT ξ₀ B.ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phaseF σ JS JT ξ₀ B.ψ w x‖ = 1 from hn _]; simp
  rw [h1, h1, Bf.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB1 x u v _ _ rfl rfl
end GlobalTheory.FinLatUnitF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RationalLatticeSelfDual
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lattice_self_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  first | exact @_root_.GlobalTheory.RatAnnihF.ratLF_annihilator_k | exact _root_.GlobalTheory.RatAnnihF.ratLF_annihilator_k | (intros; apply _root_.GlobalTheory.RatAnnihF.ratLF_annihilator_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpEtaA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF
namespace PositivityTheory.ThKW.Eta
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem local_norm_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ)
    (h1 : 2 * (u : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : 2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    u ∈ GlobalTheory.QuadSymbol.normGroup F E (Fv F v) := by
  obtain ⟨δ, b, hδ, hb0, hb1, hbb⟩ :=
    GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)
  have hbb' : b 1 * b 1 = algebraMap F E δ := hbb
  refine (GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb').2 ?_
  rcases _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK F E σ B hB v with ⟨τ⟩ | ⟨w, hw⟩
  · obtain ⟨τ⟩ := τ
    have hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ := by rw [← map_mul, hbb', AlgHom.commutes]
    have hs0 : τ (b 1) ≠ 0 := (map_ne_zero τ).2 (b.ne_zero 1)
    have h20 : (2 : Fv F v) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    refine ⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩
    rw [← hs]
    field_simp
    ring
  · have hv2 : Valued.v (2 : Fv F v) = 1 := by
      have e : (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
      rw [e]
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_
      refine le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h => (hB.inert v w hw).1 ?_)
      exact (v.valuation_lt_one_iff_mem 2).1 h
    have a1 : Valued.v (2 * (u : Fv F v)) ≤ 1 := h1
    have a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1 := h2
    rw [map_mul, hv2, one_mul] at a1 a2
    have hu : Valued.v (u : Fv F v) = 1 := by
      refine le_antisymm a1 ?_
      have hm := congrArg Valued.v u.mul_inv
      rw [map_mul, map_one] at hm
      rw [← hm]
      exact mul_le_of_le_one_right' a2
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.InertUnitNorm.unit_eq_mul_conj_k F E σ B hB v w hw (_root_.GlobalTheory.T.inert_completion_isField F E σ B hB v w hw) u hu
    obtain ⟨x, y, rfl⟩ := tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by
      have hx := b.sum_repr x
      rw [Fin.sum_univ_two, hb0] at hx
      exact hx.symm⟩) z
    refine ⟨x, y, tensor_inj (F := F) (E := E) ?_⟩
    have e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb', ← IsScalarTower.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply']
    rw [hz, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hb1,
      TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]
    ring
end PositivityTheory.ThKW.Eta
end
end
end

