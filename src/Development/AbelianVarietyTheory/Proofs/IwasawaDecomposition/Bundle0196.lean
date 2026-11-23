module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecLinear

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lieG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (hY : Y ∈ lieG G) : X + Y ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  have h2 : Yᴴ * G + G * Y = 0 := hY
  show (X + Y)ᴴ * G + G * (X + Y) = 0
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]

theorem lieG_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (a • X)ᴴ * G + G * (a • X) = 0
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

theorem gard_add (hσ : IsURepOn (UJset ε) σ) {φ ψ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ)
    (w : H) : gard ε σ (φ + ψ) w = gard ε σ φ w + gard ε σ ψ w := by
  unfold gard
  rw [← integral_add (hφ.integrable (continuous_orbit hσ w)) (hψ.integrable (continuous_orbit hσ w))]
  simp only [Pi.add_apply, add_smul]

theorem gard_smul (a : ℝ) (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (w : H) :
    gard ε σ (a • φ) w = (a : ℂ) • gard ε σ φ w := by
  unfold gard
  rw [← integral_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Complex.coe_smul]

theorem dRep_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ w ∈ smSub G (trRep σ P), (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep (trRep σ P) (X + Y) w = dRep (trRep σ P) X w + dRep (trRep σ P) Y w) ∧ ∀ (a : ℝ), ∀ X ∈ lieG G, dRep (trRep σ P) (a • X) w = (a : ℂ) • dRep (trRep σ P) X w := by
  intro n ε H _ _ _ σ P G hP h hσ w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  refine ⟨fun X hX Y hY => ?_, fun a X hX => ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.SmVec.dRep_gard n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_add_right, inner_dRep hG hπ hu hw hX, inner_dRep hG hπ hu hw hY,
      inner_dRep hG hπ hu hw (lieG_add hX hY), (hψ X).2 hX, (hψ Y).2 hY, (hψ _).2 (lieG_add hX hY), map_add,
      gard_add hσ (hψ X).1 (hψ Y).1, inner_add_left]
    ring
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.SmVec.dRep_gard n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_smul_right, inner_dRep hG hπ hu hw hX,
      inner_dRep hG hπ hu hw (lieG_smul a hX), (hψ X).2 hX, (hψ _).2 (lieG_smul a hX), map_smul,
      gard_smul, inner_smul_left, Complex.conj_ofReal]
    ring

end GlobalTheory.SmVecLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultGelf

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}

theorem mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem isURep (M : DSModel V S) (τ : D.what₂.Tau) : IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) :=
  isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1

theorem rder_apply (hT : IsMultMap θ M J χ T) [inst : DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  letI : DecidableEq D.what₂.Tau := fun a b => Classical.propDecidable (a = b)
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := _root_.GlobalTheory.SmVec.sobCont_repr _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u)
      (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hT.equiv τ _ (exp_mem_UH hG hX t)
      (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (_root_.GlobalTheory.SmVecDeriv.hasDerivAt_word _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hT τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hT τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hT τ v Z w _ rfl

theorem gelf_apply : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  intro D θ V S M J χ _ T hT _ τ k v w hw
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hT τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

end GlobalTheory.MultGelf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwiseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ), (∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i, B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) → ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  first | exact @GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | exact GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | (intros; apply GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLocalPairMapAdelic
section
noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem pm_mulsF_of_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hh : h ∈ S.Uloc v) : MulsF S v hv 1 h := by
  rw [S.UlocAlt v hv] at hh
  obtain ⟨hg, h2⟩ := (Subgroup.mem_inf.1 hh).2
  exact ⟨hg, fun x => by rw [one_smul]; exact h2 x⟩

theorem pm_mulsF_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {a b : ℤ} {g h : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hg : MulsF S v hv a g) (hh : MulsF S v hv b h) :
    MulsF S v hv (b * a) (g * h) := by
  obtain ⟨ha, ha'⟩ := hg
  obtain ⟨hb, hb'⟩ := hh
  refine ⟨Subgroup.mul_mem _ ha hb, fun x => ?_⟩
  have h1 := ha' ⟨h.1 *ᵥ x.1, (hb x.1).1 x.2⟩
  have h2 := hb' x
  rw [← h2, ← h1, mul_smul]
  congr 3
  apply Subtype.ext
  simp [Matrix.mulVec_mulVec]

theorem pm_gen (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : Type} [Field k] {C : Type} (y : C → GA σ J)
    (hy : Function.Surjective (fun c => (Quotient.mk'' (y c) : Cls S)))
    (q : C → Pr (𝓞 E) (Fin n → E) k)
    (h1 : ∀ (c c' : C) (γ : GL (Fin n) E) (a : ℤ), MulsF S v hv a (bc (prV (E := E) v)
      ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1)) →
      (q c').act (glE γ) = (q c).dil (a : k))
    (h2 : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → (q c').act (glE γ) = q c →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1) ∈ S.Uloc v) :
    ∃ p : GA σ J → Pr (𝓞 E) (Fin n → E) k, PMap S v hv p ∧ (∀ c, p (y c) = q c) ∧
      ∀ x, ∃ c γ, p x = (q c).act (glE γ) := by
  have hpres : ∀ x : GA σ J, ∃ (c : C) (γ : GL (Fin n) E) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      γ ∈ UJ (σ : E →+* E) J ∧ κ ∈ S.U ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ := by
    intro x
    obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
    obtain ⟨hh', hhm, kk, hkm, heq⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)
    refine ⟨c, γ, kk.1, hγ, Subgroup.mem_subgroupOf.1 hkm, ?_⟩
    rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]
  choose cc gg kk hgg hkk hx using hpres
  have hloc : ∀ κ ∈ S.U, bc (prV (E := E) v) κ ∈ S.Uloc v := fun κ hκ => ((S.U_eq κ).1 hκ).2 v
  have hmov : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ⁻¹ * γ') * (y c').1) =
        bc (prV (E := E) v) κ * bc (prV (E := E) v) δ * (bc (prV (E := E) v) κ')⁻¹ := by
    intro c c' γ γ' κ κ' δ h
    rw [← map_inv, ← map_mul, ← map_mul, map_mul (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))), map_inv]
    congr 1
    have h' := eq_mul_inv_of_mul_eq h
    rw [mul_assoc, mul_assoc, h']
    group
  have hact : ∀ (c' : C) (γ γ' : GL (Fin n) E),
      ((q c').act (glE (γ⁻¹ * γ'))).act (glE γ) = (q c').act (glE γ') := by
    intro c' γ γ'
    rw [Pr.act_act, ← glE_mul, mul_inv_cancel_left]
  have key : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (a : ℤ),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      MulsF S v hv a (bc (prV (E := E) v) δ) →
      (q c').act (glE γ') = ((q c).act (glE γ)).dil (a : k) := by
    intro c c' γ γ' κ κ' δ a hκ hκ' h hδ
    have hm := pm_mulsF_mul S v hv (pm_mulsF_mul S v hv (pm_mulsF_of_mem S v hv _ (hloc κ hκ)) hδ)
      (pm_mulsF_of_mem S v hv _ (inv_mem (hloc κ' hκ')))
    rw [one_mul, mul_one, ← hmov c c' γ γ' κ κ' δ h] at hm
    rw [← hact c' γ γ', h1 c c' _ a hm, Pr.act_dil]
  have key1 : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ →
      (q c').act (glE γ') = (q c).act (glE γ) := by
    intro c c' γ γ' κ κ' hκ hκ' h
    have := key c c' γ γ' κ κ' 1 1 hκ hκ' (by rw [h, mul_one])
      (pm_mulsF_of_mem S v hv _ (by rw [map_one]; exact one_mem _))
    rwa [Int.cast_one, Pr.dil_one] at this
  refine ⟨fun x => (q (cc x)).act (glE (gg x)), ⟨fun γ _ x x' h => ?_, fun x δ => ⟨fun h => ?_, fun h => ?_⟩,
    fun x δ a h => ?_⟩, fun c => ?_, fun x => ⟨_, _, rfl⟩⟩
  · show (q (cc x')).act _ = ((q (cc x)).act _).act _
    rw [Pr.act_act, ← glE_mul]
    refine key1 _ _ _ _ (kk x) (kk x') (hkk x) (hkk x') ?_
    rw [← hx x', h, map_mul]
    conv_lhs => rw [hx x]
    simp only [mul_assoc]
  · have h' : (q (cc (x * δ))).act (glE (gg (x * δ))) = (q (cc x)).act (glE (gg x)) := h
    rw [← hact _ (gg x)] at h'
    have h3 := h2 _ _ _ (mul_mem (inv_mem (hgg x)) (hgg (x * δ))) (Pr.act_injective _ h')
    rw [hmov _ _ _ _ (kk x) (kk (x * δ)) δ.1 (by rw [← hx x, ← hx (x * δ)]; rfl)] at h3
    have h4 := mul_mem (mul_mem (inv_mem (hloc _ (hkk x))) h3) (hloc _ (hkk (x * δ)))
    rwa [← mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left] at h4
  · have := key _ _ _ _ (kk x) (kk (x * δ)) δ.1 1 (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl)
      (pm_mulsF_of_mem S v hv _ h)
    rwa [Int.cast_one, Pr.dil_one] at this
  · exact key _ _ _ _ (kk x) (kk (x * δ)) δ.1 a (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) h.2.2
  · have := key1 c (cc (y c)) 1 (gg (y c)) 1 (kk (y c)) (one_mem _) (hkk _)
      (by rw [← hx (y c), map_one, one_mul, mul_one])
    rwa [glE_one, Pr.act_refl] at this

end Gen


set_option maxHeartbeats 1000000 in
theorem exists_pmap : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  intro D u A i hi P K fMe hF hJ v
  obtain ⟨p, h1, h2, h3⟩ := pm_gen K.lev (A.eV v).1 (A.eV v).2 K.y K.y_bij.2 (pc P v)
    (_root_.GlobalTheory.LevelHecke.MovePair.pc_act_of_mulsF D u A i hi P K fMe hF v) (GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel D u A i hi P K fMe hF hJ v)
  refine ⟨p, h1, h2, fun x => ?_⟩
  obtain ⟨c, γ, h⟩ := h3 x
  rw [h]
  exact (pc_ok P v c).act _

end GlobalTheory.LevelHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem jMt_injective (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

theorem carrier_subset (μ : D.what₂.Tup) (j : ℕ) : ∀ m ∈ (D.what₂.MtLat μ j).carrier, m ∈ Set.range (D.what₂.jMt μ j) := by
  rintro _ ⟨c, rfl⟩
  refine Finset.sum_induction _ (fun m => m ∈ Set.range (D.what₂.jMt μ j)) ?_ ⟨0, map_zero _⟩ fun v hv => ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · obtain ⟨x, rfl⟩ := D.what₂.MtLat_sub μ j v hv
    exact ⟨D.what₂.OtoLL (c (D.what₂.jMt μ j x)) • x, map_smulₛₗ _ _ _⟩

variable {R : RealDat D A Ks} {F : Face D A}


end Main

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Comparison₂

end GlobalTheory.Mem.LiftForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueOneVectorStepHaarMeasure
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_unique_stepRel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (μ' : Measure (HA (AF F) σ J')), 2 ≤ M → StepData σ J x a B J' → μ'.IsHaarMeasure → (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure ∧ StepRel s σ J x a B J' μ μ') ∧ ∀ μ₁ μ₂ : Measure (HA (AF F) σ J), StepRel s σ J x a B J' μ₁ μ' → StepRel s σ J x a B J' μ₂ μ' → μ₁ = μ₂ := by
  intro F E _ _ _ _ _ σ hcm d b s M J x a B J' μ' hM hsd hμ'
  have : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨ν, hν, hνu⟩ := _root_.GlobalTheory.GaugeEx.existsUnique_isStdX F E σ hcm d b s (M + 1) J a (by omega) hsd.1 hsd.2.1
  obtain ⟨-, ⟨e, he, heu⟩, hcont⟩ := _root_.GlobalTheory.FrameStep.frameStep F E σ hcm (AF F) M J x a B J' hsd
  obtain ⟨-, hinv, horb, hfin, hne⟩ :=
    _root_.GlobalTheory.GaugeEx.StdProp.stdX_props F E σ hcm d b s (M + 1) J x a ν hsd.1 hsd.2.1 hsd.2.2.1 hν
  obtain ⟨hc1, hc2⟩ := hcont e he
  constructor
  · have : (μ'.map e.symm).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ' e.symm hc2 hc1
    obtain ⟨μ, hμ, hint⟩ := _root_.GlobalTheory.GaugeWeil.weil_formula (HA (AF F) σ J) (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)
      (ratTup (F := F) (AF F) x) (μ'.map e.symm) ν this hfin hne hinv horb
    refine ⟨μ, hμ, fun ν' hν' e' he' => ?_⟩
    obtain rfl := hνu ν' hν'
    obtain rfl := heu e' he'
    exact hint
  · intro μ₁ μ₂ h₁ h₂
    have k₁ := h₁ ν hν e he
    have k₂ := h₂ ν hν e he
    classical
    let t : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
      if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y then h.choose else 1
    have ht : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) →
        t y • ratTup (F := F) (AF F) x = y := fun y hy => by
      simp only [t, dif_pos hy]
      exact hy.choose_spec
    exact Measure.ext_of_lintegral _ fun f hf => (k₁ f hf t ht).trans (k₂ f hf t ht).symm

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumOrientedExists
section
open Formalism.BasicNotions Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem vacuum_oriented_exists : ∀ D : D7, VacExistsO D := GlobalTheory.VacuumO.vacExists

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volumesAgreeAdelic_of_trueVolume : ∀ D : D7, letI := D.host.cmStar; (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  first | exact @GlobalTheory.Mem.Vol.volTieG_of_trueVol | exact GlobalTheory.Mem.Vol.volTieG_of_trueVol | (intros; apply GlobalTheory.Mem.Vol.volTieG_of_trueVol <;> assumption)
end

