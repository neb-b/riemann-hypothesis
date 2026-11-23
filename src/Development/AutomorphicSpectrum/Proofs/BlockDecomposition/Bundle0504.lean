module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspaceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positivity_pulls_back_to_subspace : ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (y.conjTranspose * G * y) S → ∃ T : Submodule ℂ (Fin m → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupInductionGenerators
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Transfer

section Field

variable {F₀ : Type} [Field F₀] {n : ℕ}

theorem block_matrix_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose {R : Type} (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E)ᵀ = blk4 Aᵀ Cᵀ Bᵀ Eᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem cT_mul (σ : F₀ →+* F₀) {N : ℕ} (g h : Matrix (Fin N) (Fin N) F₀) : cT σ (g * h) = cT σ h * cT σ g := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_blk4 (σ : F₀ →+* F₀) (A B C E : Matrix (Fin n) (Fin n) F₀) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, block_matrix_map, blockMatrixTwoByTwoFin_transpose]

theorem cT_zero (σ : F₀ →+* F₀) : cT σ (0 : Matrix (Fin n) (Fin n) F₀) = 0 := by
  ext i j; simp [cT]

theorem cT_one (σ : F₀ →+* F₀) : cT σ (1 : Matrix (Fin n) (Fin n) F₀) = 1 := by
  ext i j; simp [cT, Matrix.one_apply, eq_comm]

theorem cT_neg (σ : F₀ →+* F₀) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (-x) = -cT σ x := by
  ext i j; simp [cT]

theorem cT_cT {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (cT σ x) = x := by
  ext i j; simp [cT, hσ]

theorem isUnit_det_cT (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (cT σ a).det := by
  have e : (cT σ a).det = σ a.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e]; exact ha.map σ

theorem mA_isUnit_det (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (mA σ a).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 a⁻¹ 0 0 (cT σ a)) ?_
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv _ ha
  have h2 : (cT σ a)⁻¹ * cT σ a = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_cT σ ha)
  rw [mA, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2, block_matrix_one]

theorem nB_isUnit_det (b : Matrix (Fin n) (Fin n) F₀) : IsUnit (nB b).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 1 (-b) 0 1) ?_
  rw [nB, submatrix_fromBlocks_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel, neg_mul, neg_neg, neg_zero, neg_add_cancel, block_matrix_one]

theorem Jm_isUnit_det : IsUnit (EC.Jm F₀ n).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 0 (-1) 1 0) ?_
  rw [EC.Jm, submatrix_fromBlocks_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel, neg_mul, neg_neg, neg_zero, neg_add_cancel, block_matrix_one]

theorem mA_isUnitary {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) :
    IsUnitary σ (EC.Jm F₀ n) (mA σ a) := by
  have h1 : cT σ a * (cT σ a)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_cT σ ha)
  have h2 : cT σ (cT σ a)⁻¹ * a = 1 := by
    have h := congrArg (cT σ) h1
    rwa [cT_mul, cT_cT hσ, cT_one] at h
  unfold IsUnitary EC.Jm mA
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel, h1, h2]

theorem nB_isUnitary {σ : F₀ →+* F₀} {b : Matrix (Fin n) (Fin n) F₀} (hb : cT σ b = b) :
    IsUnitary σ (EC.Jm F₀ n) (nB b) := by
  unfold IsUnitary EC.Jm nB
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, cT_one, hb, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel, add_neg_cancel]

theorem Jm_isUnitary (σ : F₀ →+* F₀) : IsUnitary σ (EC.Jm F₀ n) (EC.Jm F₀ n) := by
  unfold IsUnitary EC.Jm
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, cT_one, cT_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel]

theorem isUnitary_mul {σ : F₀ →+* F₀} {N : ℕ} {J g h : Matrix (Fin N) (Fin N) F₀} (hg : IsUnitary σ J g)
    (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul]
  calc cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hg, hh]

end Field

variable {D : D7} {n : ℕ}

theorem sig_sig (x : D.host.E) :
    (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x :=
  star_star x

theorem cT_sig_eq {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

theorem map_mA (a : Matrix (Fin n) (Fin n) D.host.E) :
    (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a).map (incA D) =
      blk4 (rat a) 0 0 (adj (rat a⁻¹)) := by
  change (blk4 a 0 0 (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) = _
  rw [block_matrix_map, cT_sig_eq, ← Matrix.conjTranspose_nonsing_inv, ← rat_conjTranspose]
  simp only [Matrix.map_zero _ (map_zero (incA D))]
  rfl

theorem map_nB (b : Matrix (Fin n) (Fin n) D.host.E) :
    (nB b).map (incA D) = blk4 1 (rat b) 0 1 := by
  change (blk4 1 b 0 1).map (incA D) = _
  rw [block_matrix_map]
  show blk4 (rat 1) (rat b) (rat 0) (rat 1) = _
  rw [rat_one, rat_zero]

theorem map_Jm : (EC.Jm D.host.E n).map (incA D) = blk4 0 1 (-1) 0 := by
  rw [EC.Jm, block_matrix_map]
  show blk4 (rat 0) (rat 1) (rat (-1)) (rat 0) = _
  simp only [rat_zero, rat_one, rat_neg]

theorem ratPts_transfer : RatPts → ∀ (D : D7) (n : ℕ), FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n → ∀ S : G D n → Prop, (∀ g h, S g → S h → S (g * h)) → (∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → S g) → (∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → S g) → (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → S g) → ∀ γ ∈ GF D n, S γ := by
  intro hR D n hF S hmul hm hn hw γ hγ
  obtain ⟨h1, h2, -⟩ := hR D n
  obtain ⟨g, hgu, hgU, hg⟩ := h1 γ hγ
  let T : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E → Prop := fun M =>
    IsUnit M.det ∧ IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (EC.Jm D.host.E n) M ∧
      ∀ γ' : G D n, mat γ' = M.map (incA D) → S γ'
  have hprod : ∀ M₁ M₂, T M₁ → T M₂ → T (M₁ * M₂) := by
    rintro M₁ M₂ ⟨u₁, U₁, s₁⟩ ⟨u₂, U₂, s₂⟩
    refine ⟨by rw [Matrix.det_mul]; exact u₁.mul u₂, isUnitary_mul U₁ U₂, fun γ' e => ?_⟩
    obtain ⟨γ₁, -, e₁⟩ := h2 M₁ u₁ U₁
    obtain ⟨γ₂, -, e₂⟩ := h2 M₂ u₂ U₂
    have e' : γ' = γ₁ * γ₂ := mat_injective' (by rw [e, mat_mul', e₁, e₂, Matrix.map_mul])
    rw [e']
    exact hmul _ _ (s₁ _ e₁) (s₂ _ e₂)
  have hmA : ∀ a : Matrix (Fin n) (Fin n) D.host.E, IsUnit a.det →
      T (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a) := by
    intro a ha
    refine ⟨mA_isUnit_det _ ha, mA_isUnitary sig_sig ha, fun γ' e => ?_⟩
    let a' : GL (Fin n) (AE D) := ⟨rat a, rat a⁻¹,
      by rw [← rat_mul, Matrix.mul_nonsing_inv _ ha, rat_one],
      by rw [← rat_mul, Matrix.nonsing_inv_mul _ ha, rat_one]⟩
    exact hm γ' a' (e.trans (map_mA a))
  have hnB : ∀ b : Matrix (Fin n) (Fin n) D.host.E, cT (D.sp.cm.sig : D.host.E →+* D.host.E) b = b → T (nB b) := by
    intro b hb
    refine ⟨nB_isUnit_det b, nB_isUnitary hb, fun γ' e => hn γ' (rat b) ?_ (e.trans (map_nB b))⟩
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hJ : T (EC.Jm D.host.E n) :=
    ⟨Jm_isUnit_det, Jm_isUnitary _, fun γ' e => hw γ' (e.trans map_Jm)⟩
  exact (hF T hprod hmA hnB hJ g hgu hgU).2.2 γ hg

end GlobalTheory.CompanionTheory.EisCovar.Transfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexEqCard
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeAct

theorem hint_mul_const {H : Type} [Group H] (K : Subgroup H) (v : H → ℂ) (c : ℂ) :
    hint K (fun z => v z * c) = hint K v * c := by
  by_cases hc : c = 0
  · subst hc
    simp [hint]
  have hS : rStab (fun z => v z * c) = rStab v := by
    ext k
    constructor
    · intro hk z
      exact mul_right_cancel₀ hc (hk z)
    · intro hk z
      show v (z * k) * c = v z * c
      rw [hk z]
  unfold hint
  rw [hS, mul_assoc]
  congr 1
  have e := smul_finsum c (fun q : H ⧸ rStab v ⊓ K => v q.out)
  simp only [smul_eq_mul] at e
  rw [mul_comm, e]
  exact finsum_congr fun q => mul_comm _ _

theorem relIndex_eq_card {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') : K'.relIndex K = X.card := by
  let φ : {x // x ∈ X} → K ⧸ K'.subgroupOf K := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ K'.subgroupOf K)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxy)
      exact Subtype.ext ((hX y.1 (hXK _ y.2)).unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  show Nat.card (K ⧸ K'.subgroupOf K) = _
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem finsum_left {G : Type} [Group G] (K' : Subgroup G) (φ : G → ℂ) (hφ : ∀ g, ∀ k ∈ K', φ (g * k) = φ g) (x : G) :
    ∑ᶠ q : G ⧸ K', φ (x * q.out) = ∑ᶠ q : G ⧸ K', φ q.out := by
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (G ⧸ K')))
  refine finsum_congr fun q => ?_
  have e : (MulAction.toPerm x : Equiv.Perm (G ⧸ K')) q = ((x * q.out : G) : G ⧸ K') := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [e]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (x * q.out)
  show φ (x * q.out) = φ ((x * q.out : G) : G ⧸ K').out
  rw [hs, hφ _ _ s.2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ind_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GLw a w × GLw b w) W)
    (u : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom))
    (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (g : GLw n w) :
    u.1.1 (blk h w m Y * g) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) • ρ m (u.1.1 g) := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) (GlobalTheory.LeviFubini.levH_blk h w m Y)
    simpa [GlobalTheory.LeviFubini.levH] using this
  have := GlobalTheory.SmGL.parInd_law _ _ u ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ g
  rw [hl] at this
  rw [GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w m]
  simpa using this

theorem hk_ind_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W), ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X, ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y)) := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX W _ _ ρ f hf u hu x hx lw
  have hfr : ∀ g, ∀ k ∈ K', f (g * k) = f g := fun g k hk => by
    simpa using hf.2.2.2 1 K'.one_mem k hk g
  have hur : ∀ g, ∀ k ∈ K', u.1.1 (g * k) = u.1.1 g := fun g k hk => by
    have h1 : GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ k u = u := (hu ⟨k, hk⟩).trans (one_smul ℂ u)
    exact congrArg (fun v : GlobalTheory.SmGL.IndSp _ _ => v.1.1 g) h1

  set φ : GLw n w → ℂ := fun g => f (x⁻¹ * g) * lw (u.1.1 g) with hφdef
  have hφr : ∀ g, ∀ k ∈ K', φ (g * k) = φ g := fun g k hk => by
    simp only [hφdef]
    rw [← mul_assoc, hfr _ k hk, hur g k hk]
  have hφc : HasCompactSupport φ := by
    have h1 : HasCompactSupport fun g => f (x⁻¹ * g) := hf.2.2.1.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    exact h1.mul_right
  have hcard : K'.relIndex (GlobalTheory.LFun.KGL w (n := n)) = X.card := relIndex_eq_card _ K' X hXK hX
  have hX0 : X.card ≠ 0 := by
    obtain ⟨z, ⟨hz, -⟩, -⟩ := hX 1 (GlobalTheory.LFun.KGL w (n := n)).one_mem
    exact (Finset.card_pos.2 ⟨z, hz⟩).ne'
  have hX0' : (X.card : ℂ) ≠ 0 := by exact_mod_cast hX0

  let Ψ : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] ℂ :=
    { toFun := fun v => lw (v.1.1 x)
      map_add' := fun v v' => map_add lw _ _
      map_smul' := fun c v => map_smul lw c _ }
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen f hf.2.2.1
  have e1 : lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ᶠ q : GLw n w ⧸ K', φ (x * q.out) := by
    show Ψ (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u) = _
    unfold hk
    refine (Ψ.toAddMonoidHom.map_finsum (hfin.subset fun q hq h0 => hq (by
      have h0' : f q.out = 0 := h0
      show f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u = 0
      rw [h0', zero_smul]))).trans ?_
    refine finsum_congr fun q => ?_
    show Ψ (f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u) = _
    rw [map_smul]
    simp only [hφdef, inv_mul_cancel_left]
    rfl
  have e2 := GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le (GlobalTheory.LFun.KGL w (n := n)) K' φ hle (fun k hk g => hφr g k hk)
    (by rw [hcard]; exact hX0) (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen φ hφc)
  have e3 := GlobalTheory.T.hecke_coset_sum_compact E n a b h w K' hopen hle hnorm X hXK hX φ hφr hφc
  rw [hcard] at e2
  have e4 : ∑ᶠ q : GLw n w ⧸ K', φ q.out =
      ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m =>
        hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
    have := e2.symm.trans e3
    exact mul_left_cancel₀ (inv_ne_zero hX0') this
  rw [e1, finsum_left K' φ hφr x, e4]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  funext m
  have e5 : (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      φ (blk h w m (Multiplicative.toAdd Y) * y)) = fun Y =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y) *
        (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * lw (ρ m (u.1.1 y))) := by
    funext Y
    simp only [hφdef]
    rw [ind_blk h w ρ u m _ y, map_smul, smul_eq_mul, mul_assoc]
  rw [e5, hint_mul_const]
  unfold phi3
  ring

end GlobalTheory.CompanionTheory.HeckeAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalised
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx db hdb Φ hΦ τ hτ hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, hTr, -, hB, hCl, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : LocallyCompactSpace (HermR (AF F) σ n) := (hCl n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (AF F) σ n) :=
    (hCl n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have := hdx.1
  have := hdb.1
  have : SFinite dx := inferInstance
  have : SFinite db := inferInstance
  set Th := fouH σ ψ db τ with hTh
  set S : HermR (AF F) σ n := hermOf (AF F) σ T hT with hS
  obtain ⟨hψc, hψn, -⟩ := hψ

  have hstar : ∀ (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E),
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) := by
    intro y x
    simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rfl
  have hchi : ∀ y : HermR (AF F) σ n, chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y S) := by
    intro y
    have e : Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        ∑ a, ∑ b, (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a := by
      rw [Matrix.trace_mul_comm]
      rfl
    rw [chiT, e]
    rfl
  have hsub : ∀ y z w : HermR (AF F) σ n,
      pairHerm (AF F) σ n y z + -pairHerm (AF F) σ n y w = pairHerm (AF F) σ n y (z - w) := by
    intro y z w
    simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]
    ring
  have hpc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S) := by
    have hg : Continuous (gramR (AF F) σ J : (Fin n → Fin M → AF F ⊗[F] E) → _) := hG n M J
    show Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ a, ∑ b, (z.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (gramR (AF F) σ J z.2 b a - (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a))
    refine continuous_const.mul (hTr.comp (continuous_finsetSum _ fun a _ =>
      continuous_finsetSum _ fun b _ => ?_))
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
      (((hg.comp continuous_snd).matrix_elem b a).sub continuous_const)
  have hint : Integrable (Function.uncurry fun (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) =>
      Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S)))) (db.prod dx) := by
    have h0 : Integrable (fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) => Th z.1 * Φ z.2)
        (db.prod dx) := hτ.mul_prod hΦ
    have hc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S)) := hψc.comp hpc
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have := h0.aestronglyMeasurable.mul hc.aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hψn, mul_one, le_refl]
  have hL : ∀ y, Th y * (starN σ J ψ dx Φ y * chiT σ ψ T y) =
      ∫ x, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂dx := by
    intro y
    rw [integral_const_mul, starN, ← integral_mul_const, hchi]
    congr 2
    funext x
    rw [hstar, mul_assoc, ← AddChar.map_add_eq_mul, hsub]
  have hR : ∀ x, ∫ y, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂db =
      Φ x * τ (S - gramH hCM hJ (AF F) x) := by
    intro x
    have := hinv (gramH hCM hJ (AF F) x - S)
    rw [neg_sub] at this
    rw [← this, ← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

theorem mul_mem_schwartzA : ∀ (D : D7) (θ : InfFam D) (m n : ℕ) (q : (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ), q.HasTemperateGrowth → ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → (fun x => q (fun τ i j => compAt θ τ x i j) * φ x) ∈ schwartzA θ m n := by
  intro D θ m n q hq φ hφ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine Submodule.subset_span ⟨SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hq f, g, hg, ?_⟩
    funext x
    simp [mul_assoc]
    exact mul_left_comm _ _ _
  | zero =>
    convert (schwartzA θ m n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    have := (schwartzA θ m n).add_mem h₁ h₂
    convert this using 1
    funext x
    simp [mul_add]
  | smul c Φ _ h =>
    have := (schwartzA θ m n).smul_mem c h
    convert this using 1
    funext x
    simp [mul_left_comm]

end GlobalTheory.CompanionTheory.WSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTestStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_derivative_is_test : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β → ∀ X : Lie E a, IsTest (dTest X β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | exact GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest <;> assumption)
end

