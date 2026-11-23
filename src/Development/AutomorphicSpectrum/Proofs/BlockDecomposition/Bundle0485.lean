module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicScalesIsotropic
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov

theorem exists_sends_of_rat_mem_minPar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
    ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW δ hδ hp
  have hF := pfrA hcm hJ hW
  have hinc : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a b h =>
    congrFun (ratV_injective (F := F) (n := 1) (a₁ := fun _ => a) (a₂ := fun _ => b) (funext fun _ => h)) 0
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin n) E,
      (matHom _ σ J δ).1 = (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (show (((show ↥(HR (AF F) σ J) from δ) : HR (AF F) σ J) :
      GL (Fin n) (AF F ⊗[F] E)) ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) from hδ)
    exact ⟨g, (congrArg Units.val hg).symm⟩
  set Bq : Matrix (Fin (r + 1)) (Fin (r + 1)) E := cT (σ : E →+* E) Y * J * ((g : Matrix (Fin n) (Fin n) E) * X) with hBq
  have hBm : Bm σ J X Y δ = Bq.map (inclR (F := F) (AF F)) := by
    unfold Bm coefM JR
    rw [hg, hBq, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
  obtain ⟨hbt, he⟩ := (mem_minPar_iff hF).1 hp
  rw [hBm] at hbt he
  have hgX : (g : Matrix (Fin n) (Fin n) E) * X = X * Bq := by
    apply Matrix.map_injective hinc
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, ← hg]
    exact he
  have hlow : ∀ k : Fin (r + 1), k ≠ 0 → Bq k 0 = 0 := fun k hk => by
    apply hinc
    have := hbt (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk)
    simpa using this
  have hcol : (g : Matrix (Fin n) (Fin n) E) *ᵥ Xᵀ 0 = Bq 0 0 • Xᵀ 0 := by
    funext i
    have h1 := congrFun (congrFun hgX i) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (r + 1))
      (fun k _ hk => by rw [hlow k hk, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)] at h1
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h1
  have hx : Xᵀ 0 ≠ 0 := fun h0 => by
    have h1 := congrFun (congrFun hW.xy 0) 0
    rw [GlobalTheory.SiegelSet.gram_apply, h0, map_zero, LinearMap.zero_apply, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  have hb : Bq 0 0 ≠ 0 := fun h0 => hx (by
    rw [h0, zero_smul] at hcol
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) hcol
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2)
  refine ⟨(Bq 0 0)⁻¹, inv_ne_zero hb, ?_⟩
  have h3 : (g : Matrix (Fin n) (Fin n) E) *ᵥ ((Bq 0 0)⁻¹ • Xᵀ 0) = Xᵀ 0 := by
    rw [Matrix.mulVec_smul, hcol, smul_smul, inv_mul_cancel₀ hb, one_smul]
  unfold Sends
  rw [hg]
  funext i
  have h4 := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) (g : Matrix (Fin n) (Fin n) E) ((Bq 0 0)⁻¹ • Xᵀ 0) i
  rw [h3] at h4
  exact h4.symm

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBound
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem JJ_preimage_box_eq_JJ_box : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB g v v'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hmono : ∀ {a a' : kˣ}, valuation k (a : k) ≤ valuation k (a' : k) →
      ∀ b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a, b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a' := by
    intro a a' haa' b hb
    have hb' : ∀ j, valuation k (b j) ≤ valuation k (a : k) := hb
    show ∀ j, valuation k (b j) ≤ valuation k (a' : k)
    exact fun j => le_trans (hb' j) haa'
  have hmin : ∀ a a' : kˣ, ∃ r : kˣ,
      valuation k (r : k) ≤ valuation k (a : k) ∧ valuation k (r : k) ≤ valuation k (a' : k) := by
    intro a a'
    rcases le_total (valuation k (a : k)) (valuation k (a' : k)) with h | h
    exacts [⟨a, le_rfl, h⟩, ⟨a', h, le_rfl⟩]
  obtain ⟨r₁, hr₁, h₁⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.ShearLat.main g
  obtain ⟨r₂, -, h₂⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₃, -, h₃⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T' hT' v'
  obtain ⟨r₄, h₄₁, h₄₂⟩ := hmin r₁ r₂
  obtain ⟨r, hr₄, hr₃⟩ := hmin r₄ r₃
  refine ⟨r, fun t ht t' hgt => ?_⟩
  set M : Set (Fin (n + 1) → k) :=
    {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'} with hM
  have hMimage : M = (fun y => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      *ᵥ y) '' (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t' : Set (Fin (n + 1) → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      show (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) ∈
          GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, SetLike.mem_coe] using hy
  have hMc : IsCompact M := by
    rw [hMimage]
    exact (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) t').image
      (Continuous.matrix_mulVec continuous_const continuous_id)
  have hMm : MeasurableSet M := hMc.isClosed.measurableSet
  have hw : Continuous (GlobalTheory.CompanionTheory.MirPair.wt ψ n) := by
    unfold GlobalTheory.CompanionTheory.MirPair.wt
    exact continuous_subtype_val.comp (hψ.comp (continuous_apply (Fin.last n)).neg)
  have hf : Continuous fun x =>
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x :=
    hw.mul (_root_.GlobalTheory.CompanionTheory.MirPair.continuous_coef T B hT v v')
  have hsub : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t : Set (Fin (n + 1) → k)) ⊆ M :=
    fun x hx => hgt x hx
  have key := GlobalTheory.T.fourier_box_integral_vanishing ν ψ c hψ hc (n + 1) t M
    (fun x => GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x)
    (GlobalTheory.CompanionTheory.MirPair.JJ ν ψ T B M v v') hMc hMm hf (by
      intro b hb
      have hbv : ∀ j, valuation k (b j) ≤ valuation k ((c * t⁻¹ : kˣ) : k) := hb
      have hb₁ := hmono (le_trans ht (le_trans hr₄ h₄₁)) b hb
      have hb₂ := hmono (le_trans ht (le_trans hr₄ h₄₂)) b hb
      have hb₃ := hmono (le_trans ht hr₃) b hb
      have hlast : valuation k (b (Fin.last n)) < 1 :=
        lt_of_le_of_lt (le_trans (hbv (Fin.last n)) (le_trans ht (le_trans hr₄ h₄₁))) hr₁
      have hinv : ∀ x, ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M :=
        fun x => h₁ b hb₁ t' x
      have h := _root_.GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear ν ψ T T' B s hψ hT hB b M v v'
        hlast (h₂ b hb₂) hinv
      rw [h₃ b hb₃] at h
      exact h)
  rw [Set.inter_eq_right.2 hsub] at key
  exact key.symm

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInduction
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_threshold_mem_box {m : ℕ} (y : Fin m → k) (t₀ : kˣ) :
    ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ t : kˣ, valuation k (t₁ : k) ≤ valuation k (t : k) → y ∈ box m t := by
  classical
  have hstep : ∀ (S : Finset (Fin m)), ∃ t₁ : kˣ, valuation k (t₀ : k) ≤ valuation k (t₁ : k) ∧
      ∀ j ∈ S, valuation k (y j) ≤ valuation k (t₁ : k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨t₀, le_rfl, by simp⟩
    | insert a S _ ih =>
      obtain ⟨t₁, h0, h1⟩ := ih
      by_cases hle : valuation k (y a) ≤ valuation k (t₁ : k)
      · refine ⟨t₁, h0, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hle
        · exact h1 j hj
      · have hlt := lt_of_not_ge hle
        have hya : y a ≠ 0 := by
          intro h0'
          rw [h0', map_zero] at hlt
          exact not_lt_zero' hlt
        refine ⟨Units.mk0 (y a) hya, ?_, fun j hj => ?_⟩
        · simpa using h0.trans hlt.le
        · rcases Finset.mem_insert.1 hj with rfl | hj
          · simp
          · simpa using (h1 j hj).trans hlt.le
  obtain ⟨t₁, h0, h1⟩ := hstep Finset.univ
  exact ⟨t₁, h0, fun t ht j => (h1 j (Finset.mem_univ j)).trans ht⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem setIntegral_box_add (ν : Measure k) [ν.IsAddHaarMeasure] {m : ℕ} (t : kˣ) {y : Fin m → k}
    (hy : y ∈ box m t) (f : (Fin m → k) → ℂ) :
    ∫ x in (box m t : Set (Fin m → k)), f (x + y) ∂(piHaar ν m) =
      ∫ x in (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) := by
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : (piHaar ν m).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hpre : (fun x => x + y) ⁻¹' (box m t : Set (Fin m → k)) = box m t := by
    ext x
    exact (box m t).add_mem_cancel_right hy
  have := (measurePreserving_add_right (piHaar ν m) y).setIntegral_preimage_emb
    (measurableEmbedding_addRight y) f (box m t : Set (Fin m → k))
  rwa [hpre] at this

theorem wt_sub (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x - y) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x - y) (Fin.last n) = y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.sub_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem wt_add (ψ : AddChar k Circle) (n : ℕ) (x y : Fin (n + 1) → k) :
    wt ψ n (x + y) = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * wt ψ n x := by
  have h : -(x + y) (Fin.last n) = -y (Fin.last n) + -x (Fin.last n) := by
    simp only [Pi.add_apply]; ring
  simp only [wt]
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem EvVal_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T T' B s _ _ hB y v v' A hA
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨t₁, h01, h1⟩ := exists_threshold_mem_box y t₀
  obtain ⟨hc1, hc2, -⟩ := GlobalTheory.T.mirabolic_coefficient_translation T T' B s hB
  refine ⟨⟨t₁, fun t ht => ?_⟩, ⟨t₁, fun t ht => ?_⟩⟩
  · have hy := h1 t ht
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy (fun x => wt ψ n (x - y) * coef T B v v' x)
    simp only [add_sub_cancel_right] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) (T (uM (n + 1) y) v) v' =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x + y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc1]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_sub, mul_assoc]
  · have hy := h1 t ht
    have hy' : -y ∈ box (n + 1) t := neg_mem hy
    have hJ := ht₀ t (h01.trans ht)
    have key := setIntegral_box_add ν t hy' (fun x => wt ψ n (x + y) * coef T B v v' x)
    simp only [← sub_eq_add_neg, sub_add_cancel] at key
    have e1 : JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v (T' (uM (n + 1) y) v') =
        ∫ x in (box (n + 1) t : Set (Fin (n + 1) → k)), wt ψ n x * coef T B v v' (x - y)
          ∂(piHaar ν (n + 1)) := by
      simp only [JJ, hc2]
    rw [e1, key, ← hJ, JJ, ← integral_const_mul]
    simp only [wt_add, mul_assoc]

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorCommutesInfiniteGl
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

section General

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_sq_map_eq {B : LinearMap.BilinForm ℝ L} {b : Module.Basis ι ℝ L} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (φ ψ : L →ₗ⁅ℝ⁆ L)
    (hφ : ∀ X Y, B (φ X) (φ Y) = B X Y) (hψ : ∀ X, φ (ψ X) = X) :
    ∑ j, ε j • (UniversalEnvelopingAlgebra.ι ℝ (φ (b j)) * UniversalEnvelopingAlgebra.ι ℝ (φ (b j))) =
      ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)) := by
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  have h1 : ∀ j, u (φ (b j)) = ∑ i, (ε i * B (b i) (φ (b j))) • u (b i) := fun j => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (φ (b j))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have h2 : ∀ i, u (b i) = ∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j)) := fun i => by
    have e := congrArg φ (eq_sum_of_orthogonal hε horth (ψ (b i)))
    rw [hψ] at e
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hφ (b j) (ψ (b i)), hψ]
  calc ∑ j, ε j • (u (φ (b j)) * u (φ (b j)))
      = ∑ j, ε j • (u (φ (b j)) * ∑ i, (ε i * B (b i) (φ (b j))) • u (b i)) :=
        Finset.sum_congr rfl fun j _ => by rw [← h1 j]
    _ = ∑ i, ∑ j, (ε i * (ε j * B (φ (b j)) (b i))) • (u (φ (b j)) * u (b i)) := by
        simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsymm (b i)]
        congr 1
        ring
    _ = ∑ i, ε i • ((∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))) * u (b i)) := by
        simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
    _ = ∑ i, ε i • (u (b i) * u (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h2 i]

end General

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem archTraceForm_AdLie (g : archGroup E a) (X Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a ((isExpLieAlgebra E a).AdLie g X) ((isExpLieAlgebra E a).AdLie g Y) =
      archTraceForm E a X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      mat (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1 := by
    change (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1
    simp
  change Matrix.trace ((mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (X : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) *
    (mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (Y : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a))) = _
  generalize mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) = A at *
  generalize mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = C at *
  generalize mat (X : ArchMatrix E a) = x
  generalize mat (Y : ArchMatrix E a) = y
  have e : A * x * C * (A * y * C) = A * (x * y * C) := by
    calc A * x * C * (A * y * C) = A * x * (C * A) * y * C := by simp only [Matrix.mul_assoc]
      _ = A * (x * y * C) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem AdLie_AdLie_inv (g : archGroup E a) (X : (isExpLieAlgebra E a).lieSubalgebra) :
    (isExpLieAlgebra E a).AdLie g ((isExpLieAlgebra E a).AdLie g⁻¹ X) = X := by
  have e := (isExpLieAlgebra E a).Ad_inv_Ad g⁻¹ ((isExpLieAlgebra E a).ofLie X)
  rw [inv_inv] at e
  exact Subtype.ext (congrArg Subtype.val e)

theorem AdU_casimir {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0) (g : archGroup E a) :
    (isExpLieAlgebra E a).AdU g (casimir b ε) = casimir b ε := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casimir, map_sum, map_smul, map_mul, IsExpLieAlgebra.AdU_ι]
  exact sum_sq_map_eq hε horth archTraceForm_symm _ ((isExpLieAlgebra E a).AdLie g⁻¹)
    (archTraceForm_AdLie g) (AdLie_AdLie_inv g)

theorem toGL_surjective : Function.Surjective (toGL E a) := fun y => by
  refine ⟨archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y), ?_⟩
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  ext i j
  simp

theorem omegaOp_comm_rt (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  obtain ⟨u, rfl⟩ := toGL_surjective y
  rw [← infEmb_eq]
  have hrt : ∀ φ : Sm E a, smL E a (rt E a (infEmb E a u) φ) = rtInf u (smL E a φ) := fun _ => rfl
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, smL_omegaOp, hrt, uAction_rtInf,
    AdU_casimir b ε hε2 horth, hrt, smL_omegaOp]

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspace
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem gram_form_eq {m n : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (w : Fin n → ℂ) :
    star w ⬝ᵥ (y.conjTranspose * G * y).mulVec w = star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem exists_posOn_of_gram (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ))
    (h : PosOn ε (y.conjTranspose * G * y) S) :
    ∃ T : Submodule ℂ (Fin m → ℂ), PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  have key : ∀ w ∈ S, w ≠ 0 → 0 < ε * (star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w)).re := by
    intro w hw hw0
    have hpos := h w hw hw0
    rwa [gram_form_eq] at hpos
  have hinj : Function.Injective ((Matrix.mulVecLin y).domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : Fin n → ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have h1 := key w w.2 hw0
    have h2 : y.mulVec (w : Fin n → ℂ) = 0 := by simpa using hw
    simp [h2] at h1
  refine ⟨S.map (Matrix.mulVecLin y), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hv0 (map_zero _)
    rw [Matrix.mulVecLin_apply]
    exact key w hw hw0
  · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtension
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

theorem hE_mulVec_self {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J M : Matrix (Fin n) (Fin n) E) (hM : cT (σ : E →+* E) M * J * M = J) (w : Fin n → E) :
    hE σ J (M *ᵥ w) (M *ᵥ w) = hE σ J w w := by
  have key : ∀ x y : Fin n → E, hE σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have hs : (fun i => σ ((M *ᵥ w) i)) = (M.map (σ : E →+* E)) *ᵥ (fun i => σ (w i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) M w i
  rw [key, key, hs, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have : (M.map (σ : E →+* E))ᵀ *ᵥ ((J * M) *ᵥ w) = J *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have h := hM
    unfold cT at h
    rw [h]
  rw [this]

theorem exists_sends_hE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  intro F E _ _ _ _ _ σ _ n J _ γ hγ w
  obtain ⟨M, hM, e⟩ := hγ
  refine ⟨(M : Matrix (Fin n) (Fin n) E) *ᵥ w, ?_, hE_mulVec_self σ J _ hM w⟩
  have e' : (matHom _ σ J γ).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    have := congrArg (fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) e
    exact this.symm
  unfold Sends
  rw [e']
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (M : Matrix (Fin n) (Fin n) E) w i).symm

end GlobalTheory.CompanionTheory.RedCov

end
end

