module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWeylCellTranslate
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.UnipShiftU

variable {L : Type} [Field L]

theorem unipB_mul_apply_succ {n : ℕ} {X Y : GL (Fin n) L} (hX : X ∈ unipB L (Fin n)) (hY : Y ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' =
      (X : Matrix (Fin n) (Fin n) L) a a' + (Y : Matrix (Fin n) (Fin n) L) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

theorem unipB_inv_apply_succ {n : ℕ} {X : GL (Fin n) L} (hX : X ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' = -(X : Matrix (Fin n) (Fin n) L) a a' := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have e := unipB_mul_apply_succ hX (inv_mem hX) h
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hne] at e
  linear_combination -e

theorem conj_apply {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (X : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * X * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * X (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro e; apply hb; rw [e]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem inv_mul_diag {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h : ((y⁻¹ * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i), Units.val_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rw [hy.inv i b (by intro e; apply hb; rw [e]; simp), zero_mul]
  · simp

theorem swap_inversion {n : ℕ} {a a' p q : Fin n} (h : a'.val = a.val + 1) (hpq : p < q)
    (hs : Equiv.swap a a' q < Equiv.swap a a' p) : p = a ∧ q = a' := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def] at hs
  rw [Fin.lt_iff_val_lt_val] at hpq
  split_ifs at hs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem transvection_apply' {n : ℕ} (a a' : Fin n) (d : L) (i j : Fin n) :
    Matrix.transvection a a' d i j = (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

theorem ordL_one [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 := by
  unfold ordL
  rw [dite_eq_right (by simp)]
  simp
  rfl

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMemIsotropicFlagLevi
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open GlobalTheory.Orb (archMat)

namespace GlobalTheory.UAut.TorusLevi

theorem prodTens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have key : ∀ x : (A × B) ⊗[F] E, TensorProduct.prodLeft F F A B E x =
      (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x,
        Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp <;> rfl
    | tmul p e =>
      obtain ⟨p₁, p₂⟩ := p
      simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [key, key, a, b]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem adele_ext {z z' : AF F ⊗[F] E} (a : ∀ w, compInf F E w z = compInf F E w z')
    (b : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z') : z = z' := by
  classical
  have key : ∀ x : AF F ⊗[F] E, ∀ w : InfinitePlace F,
      TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)
        (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) x) w = compInf F E w x := by
    intro x w
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [map_zero (compInf F E w)]
      erw [map_zero]
      try erw [map_zero]
      try rfl
    | tmul p e => rfl
    | add x y hx hy =>
      rw [map_add (compInf F E w), ← hx, ← hy]
      erw [map_add, map_add]
      try rfl
  have hinf : Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) z' := by
    apply (TensorProduct.piLeft F E (fun w : InfinitePlace F => w.Completion)).injective
    funext w
    rw [key, key, a]
  exact prodTens_ext hinf b

theorem exists_diagonal (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (s : Fin r → ℝ) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    ∃ δ : Fin r → AF F ⊗[F] E, (matHom _ σ J a).1 * adMat F Z = adMat F Z * diagonal δ := by
  classical
  have hR : ∀ w : InfinitePlace F, w.IsReal := fun w => h.1.isReal w
  let c : Fin r → Ainf F := fun i w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hR w)).symm (s i)
  refine ⟨fun i => (pairA F (c i) 1 : AF F) ⊗ₜ[F] (1 : E), ?_⟩
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  refine adele_ext (fun w => ?_) ?_
  · obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have harch : ∀ k l, archMat σ J τ (projArch σ J w a) k l =
        infEmb τ (compInf F E w ((matHom _ σ J a).1 k l)) := by
      intro k l
      show infEmb τ (((matHom _ σ J (projArch σ J w a)) : Matrix (Fin n) (Fin n) _) k l) = _
      rw [matHom_projArch]
      rfl
    have hZ : ∀ k l, infEmb τ (compInf F E w (inclR (F := F) (AF F) (Z k l))) = τ.1 (Z k l) := by
      intro k l
      simp [compInf, inclR, infEmb_tmul]
    have hev : evInf F w (pairA F (c j) 1) = c j w := rfl
    have hc : infEmb τ (compInf F E w ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E))) = (s j : ℂ) := by
      simp only [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, hev, infEmb_tmul, map_one, mul_one]
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hR w),
        ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hR w), RingEquiv.apply_symm_apply]
    have hij := congrFun (congrFun (hs w τ) i) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at hij
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Matrix.map_apply, hZ, hc, ← harch]
    simpa only [Matrix.map_apply] using hij
  · have hfin : ∀ k l, (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom ((matHom _ σ J a).1 k l) =
        (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l := fun k l =>
      congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) k l)
        (MonoidHom.mem_ker.mp ha)
    have hδ : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
        ((pairA F (c j) 1 : AF F) ⊗ₜ[F] (1 : E)) = 1 := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hfin, hδ, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem mem_parFlag (h : IsCMExt F E σ) {a : GAd σ J} (ha : a ∈ infPts σ J) (Z : Matrix (Fin n) (Fin r) E)
    (d : Fin r → ℕ) (s : Fin r → ℝ) (h0 : ∀ i, s i ≠ 0) (hs : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (s i : ℂ))) :
    a ∈ parFlag σ J Z d := by
  have hinv : ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1 = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
    intro w τ
    have h1 : archMat σ J τ (projArch σ J w a⁻¹) * archMat σ J τ (projArch σ J w a) = 1 := by
      rw [← map_mul (archMat σ J τ), ← map_mul (projArch σ J w), inv_mul_cancel, map_one, map_one]
    have h2 : diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (h0 i))]
    calc archMat σ J τ (projArch σ J w a⁻¹) * Z.map τ.1
        = archMat σ J τ (projArch σ J w a⁻¹) * (Z.map τ.1 *
            (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)))) := by
          rw [h2, Matrix.mul_one]
      _ = (archMat σ J τ (projArch σ J w a⁻¹) * (archMat σ J τ (projArch σ J w a) * Z.map τ.1)) *
            diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [hs w τ]
          simp only [Matrix.mul_assoc]
      _ = Z.map τ.1 * diagonal (fun i => (((s i)⁻¹ : ℝ) : ℂ)) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨δ, hδ⟩ := exists_diagonal h ha Z s hs
  obtain ⟨δ', hδ'⟩ := exists_diagonal h (inv_mem ha) Z (fun i => (s i)⁻¹) hinv
  exact ⟨⟨diagonal δ, blockTriangular_diagonal δ, hδ⟩, diagonal δ', blockTriangular_diagonal δ', hδ'⟩

theorem torus_mem_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J _ r X Y d _ _ _ t a ht ha
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨mem_parFlag h ha1 X d t ht fun w τ => (ha2 w τ).1, ?_⟩
  refine mem_parFlag h ha1 Y d (fun i => (t i)⁻¹) (fun i => inv_ne_zero (ht i)) fun w τ => ?_
  simpa only [Complex.ofReal_inv] using (ha2 w τ).2.1

end GlobalTheory.UAut.TorusLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixForm
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

namespace GlobalTheory.WachChain

theorem cancel_left {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O)
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin q) (Fin m) O} (h : A * X = A * Y) : X = Y := by
  ext i j
  have h1 := congrArg (fun Z => Z *ᵥ Pi.single j 1) h
  simp only [← Matrix.mulVec_mulVec] at h1
  have h2 := congrFun (hA h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem solve {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O) (Z : Matrix ι (Fin m) O)
    (h : ∀ j, ∃ w, A *ᵥ w = fun i => Z i j) : ∃ Y : Matrix (Fin q) (Fin m) O, A * Y = Z := by
  choose w hw using h
  refine ⟨Matrix.of fun k j => w j k, ?_⟩
  ext i j
  have h1 := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1

theorem mkRep {Γ O ι : Type} [Group Γ] [CommRing O] [Fintype ι] [DecidableEq ι] {q : ℕ} (A : Matrix ι (Fin q) O)
    (ρ : Γ →* Matrix ι ι O) (hA : Function.Injective A.mulVec)
    (hst : ∀ g v, ∃ w, A *ᵥ w = ρ g *ᵥ (A *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin q) O, ∀ g, A * (r' g : Matrix (Fin q) (Fin q) O) = ρ g * A := by
  have h1 : ∀ g, ∃ Y : Matrix (Fin q) (Fin q) O, A * Y = ρ g * A := fun g =>
    solve A (ρ g * A) fun j => by
      obtain ⟨w, hw⟩ := hst g (Pi.single j 1)
      refine ⟨w, ?_⟩
      rw [hw, Matrix.mulVec_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose Y hY using h1
  let f : Γ →* Matrix (Fin q) (Fin q) O :=
    { toFun := Y
      map_one' := cancel_left A hA (by rw [hY, map_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left A hA (by
        rw [hY, map_mul, Matrix.mul_assoc, ← hY h, ← Matrix.mul_assoc, ← hY g, Matrix.mul_assoc]) }
  exact ⟨f.toHomUnits, fun g => by rw [MonoidHom.coe_toHomUnits]; exact hY g⟩

theorem chain_of_lattices : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  intro Γ O _ _ _ _ n t R r ψ ϖ M rs hϖ hM0 hlast hmono hst hline
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hin : ∀ k (y : Fin n → O), (fun a => ϖ * y a) ∈ M k := fun k y =>
    hmono (Fin.zero_le k) ((hM0 _).2 ⟨y, rfl⟩)
  choose A hA hdet using fun k => GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer n ϖ (M k) hϖ0 (hin k)
  have hinj : ∀ k, Function.Injective (A k).mulVec := fun k u v huv => by
    by_contra hne
    refine hdet k ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u - v, sub_ne_zero.2 hne, ?_⟩)
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hrep : ∀ k, ∃ ρ : Γ →* GL (Fin n) O, Tw ρ r (A k) := fun k =>
    mkRep (A k) ((Units.coeHom _).comp r) (hinj k)
      (fun g v => (hA k _).1 (hst g k _ ((hA k _).2 ⟨v, rfl⟩)))
  choose ρ hρ using hrep
  have hbb : ∀ k : Fin R, ∃ Y, A k.succ * Y = A k.castSucc := fun k =>
    solve _ _ fun j => (hA k.succ _).1 (hmono (Fin.castSucc_lt_succ (i := k)).le
      ((hA k.castSucc _).2 ⟨Pi.single j 1, by funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩))
  choose bb hbbe using hbb
  choose xs hxs hxn hsup hψ using hline
  have hsW : ∀ s w, ∃ u c', A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u + fun a => c' * xs s a := by
    intro s w
    have hm := (hA (rs s).succ _).2 ⟨w, rfl⟩
    rw [hsup s, Submodule.mem_sup] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨u, rfl⟩ := (hA _ _).1 hy
    exact ⟨u, c', by rw [← hyz]; rfl⟩
  have hxW : ∀ s, ∃ w, A (rs s).succ *ᵥ w = xs s := fun s => (hA _ _).1 (hxs s)
  have hcW : ∀ s u, ∃ w, A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u := fun s u =>
    (hA _ _).1 (hmono Fin.castSucc_lt_succ.le ((hA _ _).2 ⟨u, rfl⟩))
  have hnW : ∀ s, ¬ ∃ u, A (rs s).castSucc *ᵥ u = xs s := fun s h => hxn s ((hA _ _).2 h)
  have hψW : ∀ s g, ∃ u, A (rs s).castSucc *ᵥ u =
      (r g : Matrix (Fin n) (Fin n) O) *ᵥ xs s - fun a => ((ψ s g : Oˣ) : O) * xs s a :=
    fun s g => (hA _ _).1 (hψ s g)
  choose r2 B B' C E hL using fun s => _root_.GlobalTheory.FibreLine.fibre_line n r (ψ s) (A (rs s).castSucc) (A (rs s).succ) (ρ _) (ρ _)
    (xs s) (hinj _) (hinj _) (hρ _) (hρ _) (hsW s) (hxW s) (hcW s) (hψW s)
  refine ⟨⟨ρ, A, bb, r2, B, B', C, E⟩, fun k => ((A k).map (residue O)).rank,
    ⟨fun k => ⟨hρ k, hdet k, rfl⟩, fun k => ⟨?_, (hbbe k).symm⟩, fun s => hL s⟩, ?_, ?_,
    fun s => _root_.GlobalTheory.rank_residue_succ_of_adjoin n ϖ _ _ (xs s) hϖ (fun y => (hA _ _).1 (hin _ y)) (hsW s) (hxW s) (hcW s) (hnW s)⟩
  · intro g
    apply cancel_left (A k.succ) (hinj _)
    rw [← Matrix.mul_assoc, hbbe k, hρ k.castSucc g, ← hbbe k, ← Matrix.mul_assoc, ← hρ k.succ g,
      Matrix.mul_assoc]
  · have hz : (A 0).map (residue O) = 0 := by
      ext i j
      obtain ⟨y, hy⟩ := (hM0 _).1 ((hA 0 _).2 ⟨Pi.single j 1, rfl⟩)
      have hij : A 0 i j = ϖ * y i := by
        have h1 := congrFun hy i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
      have hr : residue O ϖ = 0 :=
        (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
      simp [hij, hr]
    simp [hz]
  · obtain ⟨S, hS⟩ := solve (A (Fin.last R)) (1 : Matrix (Fin n) (Fin n) O) fun j =>
      (hA _ _).1 (by rw [hlast]; trivial)
    exact (rank_of_mul_eq_one ((A (Fin.last R)).map (residue O)) (S.map (residue O))
      (by rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)])).1

end GlobalTheory.WachChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem exists_ringEquiv_mem_iff_star {E : Type} [Field E] [NumberField E] [StarRing E] :
    ∃ σ : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E,
      ∀ (a : FractionalIdeal (𝓞 E)⁰ E) (x : E), x ∈ σ a ↔ star x ∈ a := by
  let τ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)
  have hτ : ∀ x : E, IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) τ x = star x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, star_div₀]
    rfl
  refine ⟨FractionalIdeal.ringEquivOfRingEquiv E E τ, fun a x => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg star (hτ y)).trans (star_star y)
    exact h.symm ▸ hy
  · exact ⟨star x, h, (hτ (star x)).trans (star_star x)⟩

theorem stairId_ne_zero_and_mem_rev_iff : ∀ (D : D7) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → ∀ (c : ℕ) (p : Fin c), stairId 𝔞 𝔞' c p ≠ 0 ∧ ∀ x, x ∈ stairId 𝔞 𝔞' c p.rev ↔ star x ∈ (stairId 𝔞 𝔞' c p)⁻¹ := by
  intro D 𝔞 𝔞' h0 h c p
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_mem_iff_star (E := D.host.E)
  have h1 : σ 𝔞 = 𝔞' := by
    ext x
    rw [hσ, h]
  have h2 : σ 𝔞' = 𝔞 := by
    ext x
    rw [hσ, h, star_star]
  have h0' : 𝔞' ≠ 0 := h1 ▸ (map_ne_zero_iff _ σ.injective).2 h0
  refine ⟨mul_ne_zero (pow_ne_zero _ h0) (inv_ne_zero (pow_ne_zero _ h0')), fun x => ?_⟩
  have h3 : σ (stairId 𝔞' 𝔞 c p.rev) = stairId 𝔞 𝔞' c p.rev := by
    unfold stairId
    rw [map_mul, map_inv₀, map_pow, map_pow, h1, h2]
  rw [← stairId_rev, ← hσ, h3]

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

namespace GlobalTheory.CohFieldChange

theorem subsingleton_coh_pull_iff {X X' : Scheme.{0}} {k E : Type} [Field k] [Field E] [Algebra k E]
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}
    [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X') (M.pull π)) n) ↔
      Subsingleton (coh (twist (GlobalTheory.structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  refine e₂.toEquiv.subsingleton_congr.symm.trans (Iff.trans ?_ e₁.toEquiv.subsingleton_congr)
  refine e₄.toEquiv.subsingleton_congr.symm.trans (e₃.toEquiv.subsingleton_congr.trans ?_)
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k E

theorem subsingleton_coh_pull_iff_of_isProjOver : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → ∀ M : LB Y, M.IsLB → ∀ n : ℕ, (Subsingleton (coh (twist (GlobalTheory.structureModule X) (M.pull π)) n) ↔ Subsingleton (coh (twist (GlobalTheory.structureModule Y) M) n)) := by
  intro k E _ _ _ Y X p q π H h _ M hM n
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact subsingleton_coh_pull_iff (f := p) (f' := q) H hM n

end GlobalTheory.CohFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerChartsPreimageAndGermPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem Charts.tower_preimage_germ : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  intro R _ I Y β n C γ h0 hγ e
  induction e with
  | zero =>
    intro i
    subst_vars
    refine ⟨?_, fun j z _ => ?_⟩
    · rw [h0]; rfl
    · rw [h0]
  | succ e ih =>
    intro i
    obtain ⟨hpre, hgerm⟩ := ih i
    have hp : γ (e + 1) ⁻¹ᵁ C.D (e + 1) i = C.D 0 i := by
      rw [← hγ e, Scheme.Hom.comp_preimage, C.pre, hpre]
    refine ⟨hp, fun j z hz => ?_⟩
    have hz' : γ e z ∈ C.D e i := by rw [← hpre] at hz; exact hz
    have hz'' : β e (γ e z) ∈ C.D (e + 1) i := by
      have : γ e z ∈ β e ⁻¹ᵁ C.D (e + 1) i := by rw [C.pre]; exact hz'
      exact this
    rw [← hgerm j z hz, ← C.ρ_pull e i j, ← hγ e, ← gs_pull (γ e) (β e) z _ hz'',
      ← gs_res (γ e) z (C.pre e i).ge hz']
    rfl

end GlobalTheory.FormalAlg
end

