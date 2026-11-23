module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalQuantumDeterminantIntertwining
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CapelliIntertw

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) :
    f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')

def intertw : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') where
  carrier := {z | ∀ v, T (z.1 v) = z.2 (T v)}
  mul_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
    rw [ha, hb]
  add_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add (f := _)]
    rw [ha, hb]
  algebraMap_mem' := by
    intro c v
    simp [Module.algebraMap_end_apply]

end GlobalTheory.CapelliIntertw

theorem GlobalTheory.capelli_intertw : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  intro M M' _ _ _ _ T n X Y hXY u p v
  let S := GlobalTheory.CapelliIntertw.intertw T
  let Z : Fin n → Fin n → S := fun a b => ⟨(X a b, Y a b), fun w => hXY a b w⟩
  let q : S := Polynomial.aeval (Formalism.REAL.qdet Z u) p
  have h1 : ((q : Module.End ℂ M × Module.End ℂ M').1) = Polynomial.aeval (Formalism.REAL.qdet X u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.fst ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  have h2 : ((q : Module.End ℂ M × Module.End ℂ M').2) = Polynomial.aeval (Formalism.REAL.qdet Y u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.snd ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  rw [← h1, ← h2]
  exact q.2 v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
section
noncomputable section

open Matrix

namespace GlobalTheory.LeviGA

variable {R S : Type} [CommRing R] [CommRing S] {a r : ℕ}

def blkEquiv (h : r ≤ a) : Fin r ⊕ Fin (a - r) ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

@[simp] theorem blkEquiv_inl (h : r ≤ a) (i : Fin r) : ((blkEquiv h (Sum.inl i) : Fin a) : ℕ) = i := rfl

@[simp] theorem blkEquiv_inr (h : r ≤ a) (i : Fin (a - r)) : ((blkEquiv h (Sum.inr i) : Fin a) : ℕ) = r + i := rfl


variable (R) in
def blkMat (h : r ≤ a) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin (a - r)) (Fin (a - r)) R →* Matrix (Fin a) (Fin a) R where
  toFun p := Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blkGL (h : r ≤ a) : GL (Fin r) R × GL (Fin (a - r)) R →* GL (Fin a) R :=
  (Units.map (blkMat R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem blkGL_val (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) =
      Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R)) :=
  rfl

theorem blkGL_apply (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin r ⊕ Fin (a - r)) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) (blkEquiv h i) (blkEquiv h j) =
      Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R) i j := by
  rw [blkGL_val, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem blkGL_block (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin a) :
    ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (blkGL h p : Matrix (Fin a) (Fin a) R) i j = 0 := by
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · left; simp
  · right; simp
  · right; simp
  · left; simp

theorem exists_blkGL (h : r ≤ a) (m : GL (Fin a) R)
    (hm : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (m : Matrix (Fin a) (Fin a) R) i j = 0) :
    ∃ p, blkGL h p = m := by
  obtain ⟨M, hM⟩ : ∃ M, M = (m : Matrix (Fin a) (Fin a) R).submatrix (blkEquiv h) (blkEquiv h) := ⟨_, rfl⟩
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inl i)) (blkEquiv h (Sum.inr j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inr i)) (blkEquiv h (Sum.inl j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h12, h21]
  have hdet : IsUnit M.det := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
  rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have hD : IsUnit M.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(hA.unit, hD.unit), Units.ext ?_⟩
  rw [blkGL_val]
  simp only [IsUnit.unit_spec]
  rw [← hMb, hM]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]

theorem map_blkGL (h : r ≤ a) (f : R →+* S) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    Units.map f.mapMatrix.toMonoidHom (blkGL h p) =
      blkGL h (Units.map f.mapMatrix.toMonoidHom p.1, Units.map f.mapMatrix.toMonoidHom p.2) := by
  apply Units.ext
  simp only [Units.coe_map, blkGL_val]
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.reindex_apply]

end GlobalTheory.LeviGA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGLHomConjPermMatrixOfBlocksMatchStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockGLHom_conj_permMatrix_of_blocks_match : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r)), (∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) → ∀ i : Fin r, (block b (b i)).card = (block b' (b' (w i))).card ∧ ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d), ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F, (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w = permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  first | exact @GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | exact GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | (intros; apply GlobalTheory.Proof.BlockConj.blockHom_conj_permGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularPrimitiveCharacters
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]


variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

end GlobalTheory.FinGL.LeviChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodesStatement
section
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_eq_linearCombination_nat_nodes : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  first | exact @GlobalTheory.CuspRep.cap_eq_sum_nodes | exact GlobalTheory.CuspRep.cap_eq_sum_nodes | (intros; apply GlobalTheory.CuspRep.cap_eq_sum_nodes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCAlpha

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def lapOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2)

def casKOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
    ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
      (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2)

def vecF (X : Lie E a) (f : Lie E a → ℂ) : Lie E a → ℂ := fun y => fderiv ℝ f y (rmul X y)

def lapF (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    (vecF E a (toL (Matrix.single i j (atEmb τ 1))) (vecF E a (toL (Matrix.single i j (atEmb τ 1))) f) +
      vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) (vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) f))

def polyF (p : Polynomial ℂ) (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (lapF E a)^[k] f

end GlobalTheory.HCAlpha

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseParamTaylorShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnPer.close_paramTaylor_shift : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) (F₀ : Fam I₀ g Λ), (0 : I → ℂ) ∈ F.V → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D) (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → (∀ i, t i = ∑ j, n j i) → ∀ (K : Charts F) (K₀ : Charts F₀) (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (Ta : Hol (K.W k) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀)) (Ta' : Hol (K.W k') →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀')), (∀ (h : Hol (K.W k)) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → (∀ (h : Hol (K.W k')) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀'), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta' h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀'))) (Ta'.toRingHom.comp (Charts.sh h)) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀))).comp Ta).toRingHom) := by
  intro I I₀ _ _ _ g D _ _ Λ _ F F₀ h0 hτ J N hN t r n hn hnn ht K K₀ l k k' k₀ k₀' h h₀ hW Ta Ta' hTa hTa'
  have htJ : ∀ i, t i ∈ J := fun i ↦ by rw [ht]; exact J.sum_mem fun j _ ↦ hn j i
  have hnil : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0 := fun s ↦ hN _ fun a ↦ htJ _
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l 0 h0
  obtain ⟨n', h1, h2, h3⟩ := GlobalTheory.PeriodFamily.taylor_sum_sub_value_eq_sum_sqZero J N hN r n hn hnn (fun (a : Fin g) z ↦ F.τ l z a)
    fun a ↦ analyticAt_pi_iff.1 hτa a
  have et : (fun i ↦ ∑ j, n j i) = t := funext fun i ↦ (ht i).symm
  rw [et] at h3
  obtain ⟨-, -, hconst, hcongr, -, -⟩ := _root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t
  have hm : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k := fun p hp ↦ K.maps h _ (hW p hp)
  refine GlobalTheory.AnPer.close_of_sliceTaylor J N hN t htJ r n' h1 h2 (K.W k) (K₀.W k₀') (fun p : Tot I₀ g ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hm _ _ (fun f p hp ↦ ?_) fun f p hp ↦ ?_
  · refine (hTa' (Charts.sh h f) p hp).trans ?_
    have e : (fun z : I → ℂ ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := by fun_prop
      filter_upwards [hc.continuousAt.eventually ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
        using Charts.fn_sh h f hz
    rw [hcongr _ _ e, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (F.τ l) p.2 hτa (f.analytic _ (hm p hp))]
    simp only [h3]
  · have hp' := K₀.maps h₀ p hp
    have e : ∀ x : D ⊗[ℂ] Hol (K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀)) x) =
        Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev (F₀.shift l p) hp')) (fun _ _ ↦ Commute.all _ _) x := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul d c =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
          Hol.ev_apply, Hol.fn_comap _ _ _ _ hp, AlgHom.id_apply]
    refine (e (Ta f)).trans ((hTa f _ hp').trans ?_)
    have e2 : (F₀.shift l p).2 = p.2 + F.τ l 0 := by simp only [Fam.shift, hτ]
    rw [e2, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hm p hp))]
    simp only [hconst, sub_self]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShift
section
open Filter Topology TopologicalSpace TensorProduct
open GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer

theorem evT_map_shA {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
    {R : Type} [CommRing R] [Algebra ℂ R] {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k')
    (y : R ⊗[ℂ] Hol (K.W k)) :
    evT R p hp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) y) =
      evT R (F.shift l p) (K.maps h p hp) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, AlgHom.comp_apply, Hol.ev_apply, Hol.ev_apply, Charts.shA_apply, Charts.fn_sh h y hp]
    rfl

theorem close_taylor_shift : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  intro I _ _ g Λ _ F F₀ K K₀ R _ _ J N hJ r m hm hmm hτ l k k' k₀ k₀' h h₀ hW ρ ρ' hρ hρ'
  rcases Classical.em (∃ p, p ∈ K₀.W k₀') with hne | hne
  swap
  · have e : ρ'.comp (Charts.sh h) =
        (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ :=
      RingHom.ext fun f ↦ GlobalTheory.tensor_hol_ext_of_values _ _ _ _ fun p hp ↦ (hne ⟨p, hp⟩).elim
    rw [e]
    exact Relation.ReflTransGen.refl
  obtain ⟨p₀, hp₀⟩ := hne
  have h0 : (0 : I → ℂ) ∈ F.V := K.base k' _ (hW p₀ hp₀)
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l _ h0
  obtain ⟨n, hn, hnn, hd⟩ := _root_.GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero J N hJ r m hm hmm (F.τ l) hτa
  have ht : ∀ i, (fun i ↦ ∑ j, m j i) i ∈ J := fun i ↦ J.sum_mem fun j _ ↦ hm j i
  have htN : ∀ s : Fin (N + 1) → I, ∏ a, (fun i ↦ ∑ j, m j i) (s a) = 0 :=
    fun s ↦ hJ _ fun a ↦ ht (s a)
  have hin : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k :=
    fun p hp ↦ K.maps h _ (hW p hp)
  obtain ⟨-, -, hconst, hgerm, -, -⟩ := taylor_formal_properties N (fun i ↦ ∑ j, m j i)
  refine close_of_sliceTaylor J N hJ _ ht r n hn hnn (K.W k) (K₀.W k₀') (fun p ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hin _ _ ?_ ?_
  · intro f p hp
    refine (hρ' (Charts.sh h f) p hp).trans ?_
    have hc : ContinuousAt (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) 0 := by fun_prop
    have e : (fun z ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      filter_upwards [hc.preimage_mem_nhds ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
      exact Charts.fn_sh h f hz
    rw [hgerm _ _ e, taylor_shear N _ htN f.fn (F.τ l) p.2 hτa (f.analytic _ (hin p hp))]
    simp only [hd]
  · intro f p hp
    refine (evT_map_shA h₀ p hp (ρ f)).trans ?_
    refine (hρ f _ _).trans ?_
    have e : (F₀.shift l p).2 = p.2 + F.τ l 0 := by
      change p.2 + F₀.τ l p.1 = _
      rw [hτ]
    rw [e]
    refine (taylor_shear N _ htN f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hin p hp))).trans ?_
    simp only [hconst, sub_self]

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_comp_of_close_includeRight : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C) (ρ : Hol W →+* R ⊗[ℂ] Hol W₀), (∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h)) → ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C, (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) → Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  exact @GlobalTheory.CloseTen.close_tensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeQcqsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_baseChange_qcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S) [CompactSpace W] [QuasiSeparatedSpace W], ContCone R F ((bc (sch.map r)).mapCone c) := by
  first
  | exact @GlobalTheory.contCone_bc_of_qcqs
  | exact GlobalTheory.contCone_bc_of_qcqs
  | (intros; apply GlobalTheory.contCone_bc_of_qcqs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLeviDatumPermBlocksMatchStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalLeviDatum_perm_blocks_match : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'), IsCuspDatum b σ → IsCuspDatum b' σ' → ∀ (w : Equiv.Perm (Fin r)) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'), (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  first | exact @GlobalTheory.FinGL.BlockMatch.blocks_match | exact GlobalTheory.FinGL.BlockMatch.blocks_match | (intros; apply GlobalTheory.FinGL.BlockMatch.blocks_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  first | (exact @GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (exact GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (intros; apply GlobalTheory.EtC.eq_pow_of_kum_eq_zero  <;> assumption)
end

