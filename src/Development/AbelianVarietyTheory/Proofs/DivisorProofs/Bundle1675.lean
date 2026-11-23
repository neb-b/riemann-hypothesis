module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormWCuspPhLe
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

theorem hasGram_norm_sum_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {N : (K →+* ℂ) → V → ℝ} (hN : GlobalTheory.AllWt.HasGram N) (σ : K →+* ℂ)
    (hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y) {ι : Type} (s : Finset ι) (y : ι → V) :
    N σ (∑ i ∈ s, y i) ≤ ∑ i ∈ s, N σ (y i) ∧ ∀ z, 0 ≤ N σ z := by
  obtain ⟨⟨n, ⟨b, X⟩, hbX⟩⟩ := hN
  letI : StarRing K := starRingOfComm
  let Φ : V →+ EuclideanSpace ℂ (Fin n) :=
    { toFun := fun y => (WithLp.equiv 2 (Fin n → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X (InfinitePlace.mk σ) y)
      map_zero' := by rw [Formalism.HermitianLatticesTheory.fcoord_zero]; rfl
      map_add' := fun y z => by rw [Formalism.HermitianLatticesTheory.fcoord_add]; rfl }
  have hΦ : ∀ y, N σ y = ‖Φ y‖ := by
    intro y
    rw [← hτ, ← (hbX (InfinitePlace.mk σ)).2 y, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]
    rfl
  refine ⟨?_, fun z => (hΦ z).symm ▸ norm_nonneg _⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ, map_sum]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun g _ => (hΦ _).symm))

theorem sum_sq_normW_cuspPh_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W) (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (B : ℝ), 0 ≤ B → GlobalTheory.AllWt.HasGram (GlobalTheory.AllWt.normW U x V dict (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g = GlobalTheory.AllWt.normW U x V dict (G + W) σ f) → (∀ (γ : LevelAut Dw l) (f : cuspW Xo c U G) (g : cuspW Xo c U (G + W)), (g : Rul Xo c) = f * pull Xo c γ u → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict G σ f) → ∀ (f : cuspW Xo c U G) (σ : c.F →+* ℂ), ∑ h : S, GlobalTheory.AllWt.normW U x V dict (G + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ^ 2 ≤ (Fintype.card S : ℝ) ^ 3 * B ^ 2 * GlobalTheory.AllWt.normW U x V dict G σ f ^ 2 := by
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hK hKW χ u B hB hGram hinv hbd f σ
  set N := GlobalTheory.AllWt.normW U x V dict (G + W) with hN
  have hconj : ∀ y, N ((starRingEnd ℂ).comp σ) y = N σ y := fun y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.petW, GlobalTheory.AllWt.petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y := by
    intro y
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      rw [h, e, hconj]
  have hnn : ∀ y, 0 ≤ N σ y := (hasGram_norm_sum_le hGram σ hτ (∅ : Finset S) (fun _ => 0)).2
  have hsum : ∀ (s : Finset S) (y : S → cuspW Xo c U (G + W)), N σ (∑ g ∈ s, y g) ≤ ∑ g ∈ s, N σ (y g) :=
    fun s y => (hasGram_norm_sum_le hGram σ hτ s y).1
  have hsmul : ∀ (a : c.F) (y : cuspW Xo c U (G + W)), N σ (a • y) = ‖σ a‖ * N σ y := fun a y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, Submodule.coe_smul, GlobalTheory.AllWt.petW_smul]
  have hunit : ∀ g : S, ‖σ (((χ g)⁻¹ : (c.F)ˣ) : c.F)‖ = 1 := by
    intro g
    have h1 : ((χ g)⁻¹) ^ (Fintype.card S) = 1 := by rw [← map_inv, ← map_pow, pow_card_eq_one, map_one]
    refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card S) ?_ Fintype.card_ne_zero
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  have hcomp : ∀ h : S, N σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
      (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ≤
        (Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f) := by
    intro h
    have hFm : (f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u ∈ cuspW Xo c U (G + W) :=
      GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW (h : LevelAut Dw l) _ u.2)
    have hP : ∀ g : S, pull Xo c (g : LevelAut Dw l) ((f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u) ∈
        cuspW Xo c U (G + W) := fun g => hK (g : LevelAut Dw l) _ hFm
    have he : ((GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
        (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h : cuspW Xo c U (G + W)) : Rul Xo c) =
          ((∑ g : S, (((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)) : cuspW Xo c U (G + W)) :
            Rul Xo c) := by
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      rfl
    rw [Subtype.ext he]
    refine (hsum _ _).trans ?_
    calc ∑ g : S, N σ ((((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)))
        ≤ ∑ _g : S, B * GlobalTheory.AllWt.normW U x V dict G σ f := by
          refine Finset.sum_le_sum fun g _ => ?_
          rw [hsmul, hunit, one_mul, hinv (g : LevelAut Dw l) ⟨_, hFm⟩ ⟨_, hP g⟩ rfl σ]
          exact hbd (h : LevelAut Dw l) f ⟨_, hFm⟩ rfl σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc _ ≤ ∑ _h : S, ((Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f)) ^ 2 :=
        Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (hnn _) (hcomp h) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

noncomputable section

namespace GlobalTheory.SphEis.Summ

theorem tor_add (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {j : ℕ}
    (μ : Fin j → ℕ) (m₀ : ℕ) :
    tor F E (fun i => (μ i : ℤ) + -(m₀ : ℤ)) = tor F E (fun i => (μ i : ℤ)) * tor F E (fun _ => -(m₀ : ℤ)) :=
  Units.ext (by
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => congrArg Units.val (_root_.zpow_add _ _ _)))

theorem summable_absDet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv ι x p k β K hK hx e hk hβ hi t ht
  classical
  have hb : 1 < bse F := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have hb0 : 0 < bse F := one_pos.trans hb
  have hfp : fixG σ J C ≤ parFlag σ J C (fun _ => 0) := fun g hg =>
    ⟨⟨1, Matrix.blockTriangular_one, by rw [Matrix.mul_one]; exact hg⟩, 1, Matrix.blockTriangular_one, by
      rw [Matrix.mul_one]; exact inv_mem hg⟩
  obtain ⟨W, B, hW, hR⟩ := _root_.GlobalTheory.SphEis.reduce_levi F E σ n J j m C D Z J₀ hF lv hlv
  choose γ hγ hγP q hq l w hw hred hle using fun i => hR (p i) (β i) (hβ i)
  have hWK : IsCompact (W * K) := hW.mul hK
  obtain ⟨m₀, hm₀⟩ := _root_.GlobalTheory.SphEis.exists_bound_exponents F E σ n J j m C D Z J₀ hF lv hlv (W * K) hWK
  have hl : ∀ i r, -(m₀ : ℤ) ≤ l i r := fun i =>
    hm₀ (q i) (hq i) (l i) (w i * k i) (Set.mul_mem_mul (hw i) (hk i)) (by
      have := mul_mem (hγ i) (hx i)
      rwa [e, ← mul_assoc, hred, mul_assoc _ (w i)] at this)
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → Fin j → ℕ, ∀ i, l i = fun r => (μ i r : ℤ) + -(m₀ : ℤ) :=
    ⟨fun i r => (l i r + m₀).toNat, fun i => funext fun r => by have := hl i r; beta_reduce; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = lv (tor F E fun _ => -(m₀ : ℤ)) := ⟨_, rfl⟩
  have hW' : IsCompact ((fun g => a * g) '' (W * K)) := hWK.image (continuous_const_mul a)
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.SphEis.card_ratPts_fixG_tor_le F E σ n J j m C D Z J₀ hF lv hlv _ hW'
  have hz : ∀ i, γ i * x i = q i * lv (tor F E fun r => (μ i r : ℤ)) * (a * (w i * k i)) := fun i => by
    rw [e, ← mul_assoc, hred, hμ, tor_add, map_mul, ← ha]
    simp only [mul_assoc]
  have hinj : ∀ i i', γ i' * x i' * (γ i * x i)⁻¹ ∈ fixG σ J C → i = i' := fun i i' h => hi i i' (by
    have h2 : x i' * (x i)⁻¹ = (γ i')⁻¹ * (γ i' * x i' * (γ i * x i)⁻¹) * γ i := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (hγP i')) (hfp h)) (hγP i))
  refine GlobalTheory.GodementSectionReduction.summable_of_count ι j (m + j) (bse F) (max (B * bse F ^ (m₀ * j)) N) t μ _ hb ht
    (fun i => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ' S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle i).trans (le_of_eq ?_)
    rw [mul_assoc, hμ]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hc : (S.image fun i => γ i * x i).card = S.card :=
      Finset.card_image_of_injOn fun i _ i' _ h => hinj i i' (by
        rw [← h, mul_inv_cancel]
        exact one_mem _)
    rw [← hc]
    refine hN μ' _ ?_ ?_ ?_
    · intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      exact mul_mem (hγ i) (hx i)
    · intro s hs s' hs' h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs'
      rw [hinj i i' h]
    · intro s hs
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hs
      exact ⟨q i, hq i, a * (w i * k i), ⟨w i * k i, Set.mul_mem_mul (hw i) (hk i), rfl⟩, by rw [hz, hS i hi']⟩

end GlobalTheory.SphEis.Summ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

def tensForm {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ) : ((κ ⊕ κ' → k) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := l₁ fun x₁ => l₂ fun x₂ => f (Sum.elim x₁ x₂)
  map_add' f g := by
    rw [← map_add (f := _)]; congr 1; funext x₁; rw [Pi.add_apply, ← map_add (f := _)]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x₁; rw [Pi.smul_apply, ← map_smul]; rfl

theorem tensForm_box {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ)
    (φ₁ : (κ → k) → ℂ) (φ₂ : (κ' → k) → ℂ) : tensForm l₁ l₂ (boxFun φ₁ φ₂) = l₁ φ₁ * l₂ φ₂ := by
  have e : (fun x₁ => l₂ fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = l₂ φ₂ • φ₁ := by
    funext x₁
    have : (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := by funext x₂; rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  change l₁ _ = _
  rw [e, map_smul, smul_eq_mul, mul_comm]

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def repl (v : Pl (F := F)) (y : κ → AF F) (x : κ → Fv F v) : κ → AF F :=
  fun i => y i - liftV v (evFin F v (y i)) + liftV v (x i)

def proj (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ y := φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x)
  map_add' Φ Ψ := by
    funext y
    rw [Pi.add_apply, ← mul_add, ← map_add (f := _)]; rfl
  map_smul' c Φ := by
    funext y
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← smul_eq_mul c, ← map_smul]; rfl

theorem proj_apply (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (Φ : (κ → AF F) → ℂ)
    (y : κ → AF F) : proj v φ₀ l Φ y = φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x) := rfl

theorem evFin_repl (v : Pl (F := F)) (y : κ → AF F) (x : κ → Fv F v) (i : κ) : evFin F v (repl v y x i) = x i := by
  simp [repl, evFin_liftV]

theorem proj_tens (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (κ → Fv F v) → ℂ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) :
    proj v φ₀ l (tens (evFin F v) φ r) = l φ • tens (evFin F v) φ₀ r := by
  funext y
  have e : (fun x => tens (evFin F v) φ r (repl v y x)) = r y • φ := by
    funext x
    have h1 : repl v y x = y + fun i => liftV v (x i - evFin F v (y i)) := by
      funext i; simp only [repl, Pi.add_apply, map_sub]; ring
    have h2 : r (repl v y x) = r y := by
      rw [h1]; exact hr _ _ fun u hu => funext fun i => at_liftV v _ u hu
    simp only [tens, evFin_repl, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [proj_apply, e, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.MixedForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.CptCoeff
open MeasureTheory Matrix ComplexConjugate

theorem mul_conj_polar (z w : ℂ) : z * conj w = (1 / 4 : ℂ) * ((((‖z + w‖ ^ 2 : ℝ) : ℂ) - ((‖z - w‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * (((‖z + Complex.I * w‖ ^ 2 : ℝ) : ℂ) - ((‖z - Complex.I * w‖ ^ 2 : ℝ) : ℂ))) := by
  have e : ∀ y : ℂ, (((‖y‖ ^ 2 : ℝ)) : ℂ) = y * conj y := fun y => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, e, e, e]
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (z * conj w - w * conj z) * Complex.I_sq

theorem integral_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    ∫ x, (((‖h x‖ ^ 2 : ℝ)) : ℂ) ∂μ = (((∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  have hi : Integrable (fun x => ‖h x‖ ^ 2) μ := hh.integrable_norm_pow two_ne_zero
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hi.aestronglyMeasurable]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    Integrable (fun x => (((‖h x‖ ^ 2 : ℝ)) : ℂ)) μ :=
  (hh.integrable_norm_pow two_ne_zero).ofReal

theorem integral_mul_conj {X : Type} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : ∫ x, f x * conj (g x) ∂μ = (1 / 4 : ℂ) *
      (((((∫⁻ x, ‖(f + g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) - (((∫⁻ x, ‖(f - g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ)) +
      Complex.I * ((((∫⁻ x, ‖(f + Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) -
        (((∫⁻ x, ‖(f - Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ))) := by
  have h1 := hf.add hg
  have h2 := hf.sub hg
  have h3 := hf.add (hg.const_smul Complex.I)
  have h4 := hf.sub (hg.const_smul Complex.I)
  rw [← integral_sq_norm h1, ← integral_sq_norm h2, ← integral_sq_norm h3, ← integral_sq_norm h4,
    ← integral_sub (integrable_sq_norm h1) (integrable_sq_norm h2),
    ← integral_sub (integrable_sq_norm h3) (integrable_sq_norm h4), ← integral_const_mul,
    ← integral_add, ← integral_const_mul]
  · congr 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_conj_polar (f x) (g x)
  · exact (integrable_sq_norm h1).sub (integrable_sq_norm h2)
  · exact ((integrable_sq_norm h3).sub (integrable_sq_norm h4)).const_mul _

theorem integral_mul_conj_map {X : Type} [MeasurableSpace X] {μ : Measure X} (P : Submodule ℂ (X → ℂ))
    (hP : ∀ f ∈ P, MemLp f 2 μ) (T : Module.End ℂ (X → ℂ)) (hT : ∀ f ∈ P, T f ∈ P)
    (hU : ∀ f ∈ P, ∫⁻ x, ‖T f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) {f g : X → ℂ} (hf : f ∈ P) (hg : g ∈ P) :
    ∫ x, T f x * conj (T g x) ∂μ = ∫ x, f x * conj (g x) ∂μ := by
  rw [integral_mul_conj (hP _ (hT f hf)) (hP _ (hT g hg)), integral_mul_conj (hP f hf) (hP g hg),
    ← map_add, ← map_sub, ← map_smul, ← map_add, ← map_sub, hU _ (P.add_mem hf hg), hU _ (P.sub_mem hf hg),
    hU _ (P.add_mem hf (P.smul_mem _ hg)), hU _ (P.sub_mem hf (P.smul_mem _ hg))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem at_infOne : At (evI F) (infOne (F := F)) := by
  intro t ht
  have h1 : t.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ht)
  refine Prod.ext ?_ ?_
  · change t.1 * 1 = 0
    rw [h1, zero_mul]
  · change t.2 * 0 = 0
    exact mul_zero _

theorem evFin_liftV_ne {v w : Pl (F := F)} (h : w ≠ v) (a : Fv F v) : evFin F w (GlobalTheory.LatVac.liftV v a) = 0 :=
  evalV_singleFin_ne h a

theorem mul_eq_zero_of_supp (S : Finset (Pl (F := F))) {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hI : ∀ t : AF F, At (evI F) t → t • A = 0) (hS : ∀ w ∈ S, ∀ t : AF F, At (evFin F w) t → t • A = 0)
    (u : Matrix (Fin n) (Fin k) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : ∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) : A * u = 0 := by
  classical
  set e : AF F := infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1 with he
  have h1 : evI F (1 - e) = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (1 - e)) = 0
    have h0 : fstA F (infOne (F := F)) = 1 := rfl
    have hl : ∀ w : Pl (F := F), fstA F (GlobalTheory.LatVac.liftV w 1) = 0 := fun w => rfl
    have : fstA F (1 - e) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [he, map_sub, map_one, map_add (f := _), map_sum, h0, Finset.sum_eq_zero fun w _ => hl w, add_zero, sub_self]
    rw [this, map_zero]
  have h2 : ∀ w ∈ S, evFin F w (1 - e) = 0 := by
    intro w hw
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sub, map_one, map_add (f := _), map_sum]
    have h0 : evFin F w (infOne (F := F)) = 0 := by
      change evalV F w (sndA F infOne) = 0
      have : sndA F (infOne (F := F)) = 0 := rfl
      rw [this, map_zero]
    have hs : ∑ x ∈ S, evFin F w (GlobalTheory.LatVac.liftV x 1) = ∑ x ∈ S, if w = x then (1 : Fv F w) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : w = x
      · subst hx; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
      · rw [if_neg hx, evFin_liftV_ne hx]
    rw [h0, hs, Finset.sum_ite_eq S w (fun _ => (1 : Fv F w)), if_pos hw, zero_add, sub_self]
  have hue : u = e • u := by
    have := hu (1 - e) h1 h2
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hA : e • A = 0 := by
    rw [he, add_smul, Finset.sum_smul, hI _ at_infOne, zero_add]
    exact Finset.sum_eq_zero fun w hw => hS w hw _ (GlobalTheory.LatVac.at_liftV w 1)
  rw [hue, Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]

theorem matrix_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ∀ u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
    ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
          om' (g, h) Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (om' (g, h) Φ) x)) =
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u Φ x) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS Φ hΦ u hu μ hμ
  letI : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hg : mat g * u = u := by
    have := mul_eq_zero_of_supp S (mat g - 1) hgI hgS u hu
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hh : u * (mat h)ᵀ = u := by
    have := mul_eq_zero_of_supp S (mat h - 1) hhI hhS uᵀ
      (fun t h1 h2 => by rw [← Matrix.transpose_smul, hu t h1 h2, Matrix.transpose_zero])
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    have := congrArg Matrix.transpose this
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at this
  have hact : actAB (cA σ) (g, h) u = u := by
    change mat g * u * (mat h)ᵀ = u
    rw [hg, hh]
  have hcomm : om' (g, h) (G.M'.co.rho B.ψ u Φ) = G.M'.co.rho B.ψ u (om' (g, h) Φ) := by
    rw [hW.impl (g, h) u Φ hΦ, hact]
  rw [← hcomm]
  exact integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf) (om' (g, h))
    (fun f hf => hW.pres (g, h) f hf) (fun f hf => hW.unit μ hμ (g, h) f hf) hΦ
    (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std u Φ hΦ)

end GlobalTheory.CptCoeff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeries
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeriesCore
open GlobalTheory.AdTh.ShortSeries


set_option maxHeartbeats 1000000 in
theorem thetaKO_eq_short_series_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (R.ωP i t (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (R.ωP i t) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i hstd H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.AdTh.MovedDatumCore.moved_datum_core D G Pl0 T0 A Ks R F hC i hstd H Dw ι hι hiso
  refine ⟨δ, ?_⟩
  intro t l₂ φ hφ hl hrt g q0 X hq bas idx x₀ vr hM hS hx hinv hbas hvr bad N h k Λ mk e Ps y hbad he hPs hh hsupp hdet
    hΛ htriv hlev hmk Y hY v a hv hR P d hd
  obtain ⟨hP, -, hV0, hW0, hVs, hWs, hVstd⟩ := RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hC i t hstd
  have hψ := hP.weil.std
  have hvac : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) :=
    (hC.thP.vP i t).1
  choose p hp using fun q => exists_finOf (Vc D i) (Wc D i) (rank_Wc i) ((δ : ℤ) • Y q)
  have hdat := hδ t l₂ φ hφ hl bad N h k Λ mk hbad ⟨hh, e, Ps, he, hPs, hsupp⟩ hΛ htriv hlev hmk Y (fun q => (p q).1)
    (fun q => (p q).2) hY hp
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin (Vc D i).rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin (Vc D i) 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ k) * cart (R.MW i (sg0 D A)) τ * compAt R.θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat (Wc D i) (fin (Wc D i) k), w = a • v} →
      latR (rank_Wc i) (latG (Wc D i) k) = latR (rank_Wc i) L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := _root_.GlobalTheory.AdTh.SplitClass.om_reads_projA D _ _ _ _ _ _ _ hP _ g (rank_Wc i) X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move (rank_Wc i) X hinv k) _ hvac' _ hR e Ps h y he hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl (hatC l₂ φ) (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hthP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h1 := hP.weil.om_pres (h, k)⁻¹ _ (hdat ▸ GlobalTheory.OrientedHeis.theta_smul _ hth :
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ωP i t (h, k) (R.vP i t)))
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  have hrd := (reads_linear_injective D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (hatC l₂ φ _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP (rank_Wc i) X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ (hatC l₂ φ) Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rcases Int.units_eq_one_or δ with rfl | rfl
  · simp only [Units.val_one, one_smul]
    rw [hpar]
    push_cast
    ring
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_neg, Int.cast_neg, Int.cast_one, ← mul_pow]
    rw [neg_mul_neg, one_mul, one_mul]
    ring

end GlobalTheory.AdTh.ShortSeriesCore
end

