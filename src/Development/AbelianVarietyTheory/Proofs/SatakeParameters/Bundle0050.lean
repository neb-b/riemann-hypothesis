module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import ReciprocityTheory.Hypotheses.GalCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublattice
section
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

noncomputable section

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem mem_std {n : ℕ} (x : Fin n → w.adicCompletion E) :
    x ∈ (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ 1 := by
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => ∀ i, Valued.v (x i) ≤ 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩ i
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    · intro i; simp
    · intro a b _ _ ha hb i
      simpa using (Valued.v.map_add (a i) (b i)).trans (max_le (ha i) (hb i))
    · intro c a _ ha i
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      show Valued.v ((c : w.adicCompletion E) * a i) ≤ 1
      rw [map_mul]
      exact mul_le_one' hc (ha i)
  · intro hx
    have e : x = ∑ i, (⟨x i, hx i⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
      simp only [Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_same]
      rw [Algebra.smul_def]
      simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def dEnt {n : ℕ} (ϖ : w.adicCompletion E) (S : Finset (Fin n)) (i : Fin n) : w.adicCompletion E :=
  if i ∈ S then ϖ else 1

theorem mem_glMap_diag {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S))
    (x : Fin n → w.adicCompletion E) :
    x ∈ glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ Valued.v (dEnt w ϖ S i) := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have hf0 : ∀ i, dEnt w ϖ S i ≠ 0 := fun i => by unfold dEnt; split_ifs <;> simp [hϖ0]
  simp only [glMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply, hd,
    Matrix.mulVec_diagonal, mem_std]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [Matrix.mulVec_diagonal, map_mul]
    exact mul_le_of_le_one_right' (hy i)
  · intro hx
    refine ⟨fun i => x i / dEnt w ϖ S i, fun i => ?_, ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ (hx i) zero_le
    · funext i
      rw [Matrix.mulVec_diagonal, mul_div_cancel₀ _ (hf0 i)]

end GlobalTheory.DiagElem

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def redS {n : ℕ} (S : Finset (Fin n)) :
    (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 →ₗ[w.adicCompletionIntegers E]
      (S → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun x i := IsLocalRing.residue _ ⟨x.1 i, (mem_std w x.1).1 x.2 i⟩
  map_add' x y := by
    funext i
    rw [Pi.add_apply, ← map_add (f := _)]
    rfl
  map_smul' c x := by
    funext i
    rw [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      ← map_mul]
    congr 1

theorem redS_surjective {n : ℕ} (S : Finset (Fin n)) : Function.Surjective (redS w S) := by
  intro c
  choose a ha using fun i : S => IsLocalRing.residue_surjective (c i)
  refine ⟨⟨fun j => if h : j ∈ S then (a ⟨j, h⟩ : w.adicCompletion E) else 0,
    (mem_std w _).2 fun j => ?_⟩, ?_⟩
  · split_ifs
    · exact (a _).2
    · simp
  · funext ⟨i, hi⟩
    change IsLocalRing.residue _ _ = _
    rw [← ha]
    congr 1
    ext
    simp [hi]

theorem glMap_diag_mem_subElem :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
      (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ →
      ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)),
        (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) →
        (haveI := GlobalTheory.RowSatakeBound.finite_residue w
         glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
           Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n)) := by
  intro E _ _ w n ϖ hϖ S d hd
  have hd' : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S) := hd
  have hϖle : Valued.v ϖ ≤ WithZero.exp (-1 : ℤ) := hϖ.le
  have hexp : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  refine ⟨⟨_, glMap_isLattice d (std _ _ n)⟩, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
  · intro x hx
    rw [mem_glMap_diag w hϖ S d hd' x] at hx
    rw [mem_std]
    intro i
    refine (hx i).trans ?_
    unfold dEnt
    split_ifs
    · exact hϖle.trans hexp.le
    · simp
  · have hk : (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype =
        LinearMap.ker (redS w S) := by
      ext x
      rw [Submodule.mem_comap, Submodule.subtype_apply, mem_glMap_diag w hϖ S d hd',
        LinearMap.mem_ker]
      have hx := (mem_std w x.1).1 x.2
      constructor
      · intro h
        funext ⟨i, hi⟩
        change IsLocalRing.residue _ _ = 0
        rw [IsLocalRing.residue_eq_zero_iff]
        apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
        have := h i
        unfold dEnt at this
        rw [if_pos hi] at this
        exact lt_of_le_of_lt (this.trans hϖle) hexp
      · intro h i
        unfold dEnt
        split_ifs with hi
        · have := congrFun h ⟨i, hi⟩
          change IsLocalRing.residue _ _ = 0 at this
          rw [IsLocalRing.residue_eq_zero_iff] at this
          rw [hϖ]
          exact le_exp_neg_one_of_lt_one (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp this)
        · rw [map_one]; exact hx i
    change Nat.card ((std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ⧸
      (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype) = _
    rw [hk, Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (redS_surjective w S)).toEquiv,
      Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
    rfl
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [mem_glMap_diag w hϖ S d hd']
    rw [mem_std] at hx
    have hr1 : Valued.v (r : w.adicCompletion E) < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hr
    intro i
    have hri : Valued.v ((r • x) i) < 1 := by
      change Valued.v ((r : w.adicCompletion E) * x i) < 1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hx i)) hr1
    unfold dEnt
    split_ifs
    · rw [hϖ]; exact le_exp_neg_one_of_lt_one hri
    · rw [map_one]; exact hri.le

end GlobalTheory.DiagElem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdic
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.LatHecke

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem mem_std_of_coord {x : Fin r → K} (hx : ∀ i, ∃ a : O, algebraMap O K a = x i) :
    x ∈ (std O K r).1 := by
  choose a ha using hx
  have hsum : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
    ext j
    simp [Finset.sum_apply, Algebra.smul_def, Pi.single_apply, ha]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem entry_of_glMap_std_le {g : GL (Fin r) K} (h : glMap g (std O K r).1 ≤ (std O K r).1)
    (i j : Fin r) : ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j := by
  have hmem : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) (Pi.basisFun K (Fin r) j) ∈
      glMap g (std O K r).1 :=
    ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  obtain ⟨a, ha⟩ := coord_of_mem_std (h hmem) i
  exact ⟨a, by simpa [Matrix.toLin'_apply] using ha⟩

theorem glMap_std_le_of_entry {g : GL (Fin r) K}
    (h : ∀ i j, ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j) :
    glMap g (std O K r).1 ≤ (std O K r).1 := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_std_of_coord fun i => ?_
  choose a ha using h
  choose b hb using coord_of_mem_std hx
  refine ⟨∑ j, a i j * b j, ?_⟩
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, ha, hb]

theorem glMap_std_eq_iff_entry (g : GL (Fin r) K) :
    glMap g (std O K r).1 = (std O K r).1 ↔
      (∀ i j, ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j) ∧
      (∀ i j, ∃ a : O, algebraMap O K a = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j) := by
  constructor
  · intro h
    have h' : glMap g⁻¹ (std O K r).1 = (std O K r).1 := by
      have := congrArg (glMap g⁻¹) h
      rw [← glMap_mul, inv_mul_cancel, glMap_one] at this
      exact this.symm
    exact ⟨entry_of_glMap_std_le h.le, entry_of_glMap_std_le h'.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (glMap_std_le_of_entry h1) ?_
    have := Submodule.map_mono (f := (Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O)
      (glMap_std_le_of_entry h2)
    have e : glMap g (glMap g⁻¹ (std O K r).1) = (std O K r).1 := by
      rw [← glMap_mul, mul_inv_cancel, glMap_one]
    exact e.ge.trans this

end Dvr

section Sub

variable {L : Type} [Field L] {n : ℕ}

theorem mem_GLint_iff_entry (S : Subring L) (g : GL (Fin n) L) :
    g ∈ GLint (Fin n) S ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ S) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ S) := by
  constructor
  · have key : ∀ u : GL (Fin n) S, ∀ i j,
        ((bc (n := Fin n) S.subtype u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ S :=
      fun u i j => ((u : Matrix (Fin n) (Fin n) S) i j).2
    rintro ⟨u, rfl⟩
    refine ⟨key u, ?_⟩
    rw [← map_inv]
    exact key u⁻¹
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix S.subtype :
        Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) L) :=
      Matrix.map_injective Subtype.val_injective
    have hM : RingHom.mapMatrix S.subtype M = (g : Matrix (Fin n) (Fin n) L) := by
      ext i j; rfl
    have hN : RingHom.mapMatrix S.subtype N = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      ext i j; rfl
    refine ⟨⟨M, N, hinj ?_, hinj ?_⟩, Units.ext hM⟩
    · rw [map_mul, hM, hN, map_one]; exact Units.mul_inv g
    · rw [map_mul, hM, hN, map_one]; exact Units.inv_mul g

end Sub

theorem glMap_std_eq_iff_mem_GLint (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      g ∈ GLint (Fin n) (Ov E w) := by
  rw [glMap_std_eq_iff_entry, mem_GLint_iff_entry]
  have key : ∀ x : w.adicCompletion E,
      (∃ a : w.adicCompletionIntegers E,
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a = x) ↔ x ∈ Ov E w :=
    fun x => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simp only [key]

end GlobalTheory.LatHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.PstExt

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [Module LL' V'] [IsScalarTower ℚ_[l] LL' V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

theorem tensCoord_mulV (c : ↥(MaximalUnramifiedExtension l)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (mulV P LL' V' c x) i = mulV P LL V c (tensCoord E (Bst P) x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]

variable (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
include hE

theorem tensCoord_stRep (g : ↥(GK K)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (stRep P ρ' g x) i = stRep P ρ g (tensCoord E (Bst P) x i) := by
  change tensCoord E (Bst P) (AlgebraTensorModule.map (ρ' g)
    (actSt P (g : GQ l)).toLinearMap x) i =
    AlgebraTensorModule.map (ρ g) (actSt P (g : GQ l)).toLinearMap
      (tensCoord E (Bst P) x i)
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

theorem mem_Dpst_coord (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dpst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dpst P ρ := by
  constructor
  · intro hx i
    obtain ⟨K', hK⟩ := (mem_Dpst P ρ').1 hx
    exact (mem_Dpst P ρ).2 ⟨K', fun g hg => by rw [← tensCoord_stRep P hE, hK g hg]⟩
  · intro hx
    choose K' hK using fun i => (mem_Dpst P ρ).1 (hx i)
    have hsum : x = ∑ i, (tensCoord E (Bst P)).symm (Pi.single i (tensCoord E (Bst P) x i)) := by
      apply (tensCoord E (Bst P)).injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single _).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => (mem_Dpst P ρ').2 ⟨K' i, fun g hg => (tensCoord E (Bst P)).injective ?_⟩
    funext j
    rw [tensCoord_stRep P hE, LinearEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h
      simp [hK j g hg]
    · simp [Pi.single_eq_of_ne h]

def dpstCoord : DpstUr P ρ' ≃ₗ[↥(MaximalUnramifiedExtension l)] (ι → DpstUr P ρ) where
  toFun x i := toUr P ρ ⟨tensCoord E (Bst P) ((toUr P ρ').symm x).1 i,
    (mem_Dpst_coord P hE _).1 ((toUr P ρ').symm x).2 i⟩
  invFun y := toUr P ρ' ⟨(tensCoord E (Bst P)).symm fun i => ((toUr P ρ).symm (y i)).1,
    (mem_Dpst_coord P hE _).2 fun i => by
      rw [LinearEquiv.apply_symm_apply]
      exact ((toUr P ρ).symm (y i)).2⟩
  map_add' x y := by
    funext i
    exact Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
  map_smul' c x := by
    funext i
    exact Subtype.ext (tensCoord_mulV P c x.1 i)
  left_inv x := Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
  right_inv y := by
    funext i
    exact Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i)

theorem isPst_of_coord (h : IsPst P ρ) : IsPst P ρ' := by
  unfold IsPst at h ⊢
  rw [(dpstCoord P hE).rank_eq, (E.restrictScalars ℚ_[l]).rank_eq, rank_fun, rank_fun, h]

end Coord

theorem isPst_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1),
    IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  intro l _ P E Ω _ _ _ Gw O _ _ _ Bw m L₁ L₂ hL r₁ h
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isPst_of_coord P (E := GlobalTheory.Pst.vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

end GlobalTheory.PstExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixed
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

theorem cycMod_eq_one_of_mem_Ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cycMod F Ω l r σ = 1 := by
  apply Units.ext
  have e := cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) r
  simp only [Nat.cast_one, map_one] at e
  simpa [cycMod] using e

theorem tame_vanish : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  intro _ hTD hEC F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v rho hA hl hrho hex
  obtain ⟨γ, hγI, hγ⟩ := hex

  have h0 : H0 rho = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro m hm
    have h1 : rho γ m = m := (Representation.mem_invariants rho m).mp hm γ
    apply hγ.1
    show rho γ m - m = rho γ 0 - 0
    rw [h1, map_zero, sub_self, sub_self]

  set χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype with hχdef
  have hχ : χ γ = 1 := cycMod_eq_one_of_mem_Ine 1 hl hA hγI
  have hdual : Subsingleton (H0 ((twDual χ rho).comp (MonoidHom.id _))) := by
    have key : ∀ φ ∈ H0 ((twDual χ rho).comp (MonoidHom.id _)), φ = 0 := by
      intro φ hφ
      have h1 : twDual χ rho γ φ = φ := (Representation.mem_invariants _ φ).mp hφ γ
      apply DFunLike.ext
      intro x
      obtain ⟨m, rfl⟩ := hγ.2 x
      have h3 := congrArg (fun ψ : TDual (ZMod (l ^ 1)) M => ψ (rho γ m)) h1
      simp only [twDual_apply, hχ, Units.val_one, one_mul] at h3
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
      show φ (rho γ m - m) = 0
      exact (LinearMap.map_sub (φ : Module.Dual (ZMod (l ^ 1)) M) (rho γ m) m).trans (sub_eq_zero.mpr h3.symm)
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext ((key a.1 a.2).trans (key b.1 b.2).symm)

  have hTD' := hTD F Ω l 1 M A rho v Nat.one_pos hA hrho
  have hinj := hTD'.2.2.2.2.1
  have h2 : Subsingleton (H2 rho) := by
    refine ⟨fun x y => hinj ?_⟩
    ext z
    rw [Subsingleton.elim z 0, map_zero, map_zero]

  have hc0 : Nat.card (H0 rho) = 1 := by
    rw [h0]; exact Nat.card_unique
  have hc2 : Nat.card (H2 rho) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩
  have he := (hEC F Ω l 1 M A rho v Nat.one_pos hA hrho).2 hl
  have hc1 : Nat.card (H1 rho) = 1 := by rw [he, hc0, hc2]
  exact ⟨h0, (Nat.card_eq_one_iff_unique.mp hc1).1, h2⟩

end GlobalTheory.StringRepresentationDecomposition
end
end

