module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.AdelicThetaSumNormLePolynomialScale
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  intro F _ _ κ _
  set L := latPi F κ with hL
  set N₀ : ℕ := Module.finrank ℤ L + 1 with hN
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ N₀)⁻¹ with hH
  have hHs : Summable fun z : L => H z := summable_inv_one_add_pow F κ
  refine ⟨N₀, N₀, ∑' z : L, H z, ?_⟩
  intro A m Ψ hm hb hint
  set f : (κ → F) → ℂ := fun ξ => Ψ (fun i => algebraMap F (AF F) (ξ i)) with hf
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  have hψ : ∀ ξ : κ → F, (fun i => evI F (algebraMap F (AF F) (ξ i))) = ψ ξ :=
    fun ξ => funext fun i => evI_algebraMap F (ξ i)
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have hA : 0 ≤ A := le_trans (by positivity) (hb 0)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have key : ∀ ξ, ‖f ξ‖ ≤ A * (m : ℝ) ^ N₀ * Lind (g ξ) := by
    intro ξ
    by_cases h : f ξ = 0
    · rw [h, norm_zero]
      have := hLnn (g ξ)
      positivity
    · have hi := hint ξ h
      have hmem : g ξ ∈ L := mem_latPi F κ _ hi
      rw [hLind, Set.indicator_of_mem hmem]
      have hb' := hb ξ
      rw [hψ ξ] at hb'
      have hpos : 0 < (1 + ‖ψ ξ‖) ^ N₀ := by positivity
      have e1 : ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb'
      have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
      have hmpos : (0 : ℝ) < m := by linarith
      have e2 : ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ ≤ (m : ℝ) ^ N₀ * H (g ξ) := by
        simp only [hH]
        calc ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ = (m : ℝ) ^ N₀ * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ N₀)⁻¹ := by
              rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
          _ ≤ (m : ℝ) ^ N₀ * ((1 + ‖g ξ‖) ^ N₀)⁻¹ := by
              gcongr
              nlinarith [norm_nonneg (ψ ξ)]
      calc ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := e1
        _ ≤ A * ((m : ℝ) ^ N₀ * H (g ξ)) := mul_le_mul_of_nonneg_left e2 hA
        _ = _ := by ring
  have hu : Summable fun ξ => A * (m : ℝ) ^ N₀ * Lind (g ξ) :=
    (hLs.comp_injective hginj).mul_left _
  have hfs : Summable fun ξ => ‖f ξ‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hu
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  have hmk : 0 ≤ A * (m : ℝ) ^ N₀ := by positivity
  calc ‖thetaSum F Ψ‖ = ‖∑' ξ, f ξ‖ := rfl
    _ ≤ ∑' ξ, ‖f ξ‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' ξ, A * (m : ℝ) ^ N₀ * Lind (g ξ) := hfs.tsum_le_tsum key hu
    _ = A * (m : ℝ) ^ N₀ * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ A * (m : ℝ) ^ N₀ * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp hmk
    _ = (∑' z : L, H z) * A * (m : ℝ) ^ N₀ := by ring

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0

theorem theta_sum_norm_bound_denominator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k :=
  LatSum.thetaSum_norm_le_pow

end PositivityTheory.ThKF0
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EvStmt
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

def AdaptedModelEvaluationAtZero : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ 1 H'.ι (iso0 n H') e ∧
      ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ),
        (Model.Pol Ma B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) =
          Model.Pol M₁ B.ψ B.emb ∧
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
section
noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F κ) in
abbrev V : Type := κ → mixedEmbedding.mixedSpace F


variable (F κ) in
abbrev Pt : Type := (κ → AF F) × (κ → AF F)

def inf (a : mixedEmbedding.mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

def emb (w : V F κ × V F κ) : Pt F κ := (fun i => inf (w.1 i), fun i => inf (w.2 i))

def IntF (a : AF F) : Prop := a.1 = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F

def IntP (w : Pt F κ) : Prop := (∀ i, IntF (w.1 i)) ∧ ∀ i, IntF (w.2 i)

def IsHaar (μ : @Measure (κ → AF F) (borel _)) : Prop := @Measure.IsAddHaarMeasure _ _ _ (borel _) μ

def nsq (μ : @Measure (κ → AF F) (borel _)) (Φ : (κ → AF F) → ℂ) : ℝ≥0∞ := ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ

structure Impl (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (s : Pt F κ →ₗ[AF F] Pt F κ) : Prop where
  pres : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ
  impl : ∀ w, ∀ Φ ∈ schA F κ, T (schr ψ (s w) Φ) = schr ψ w (T Φ)
  unit : ∀ μ, IsHaar μ → ∀ Φ ∈ schA F κ, nsq μ (T Φ) = nsq μ Φ

structure Bd (s : Pt F κ →ₗ[AF F] Pt F κ) (d : ℕ) (c : ℝ) : Prop where
  fin : ∀ w, IntP w → IntP ((d : AF F) • s w)
  inf : ∀ w : V F κ × V F κ, ∃ w', s (emb w) = emb w' ∧ ‖w'‖ ≤ c * ‖w‖

def dR (ψ : AddChar (AF F) ℂ) (w : V F κ × V F κ) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => deriv (fun t : ℝ => schr ψ (emb (t • w)) Φ x) 0

def word (ψ : AddChar (AF F) ℂ) (l : List (V F κ × V F κ)) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := l.foldr (dR ψ) Φ

def Lev (m : ℕ) (Θ : (κ → AF F) → ℂ) : Prop := ∀ u : κ → AF F, (∀ i, IntF (u i)) → ∀ x, Θ (x + (m : AF F) • u) = Θ x

section Pair

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def sOf (M : Model σ X W) (g : UA σ X.J) (h : UA σ W.J) : Pt F (Fin n × Fin d) →ₗ[AF F] Pt F (Fin n × Fin d) where
  toFun w := M.co.e (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ)
  map_add' a b := by rw [map_add (f := _), Matrix.mul_add, Matrix.add_mul, map_add (f := _)]
  map_smul' c a := by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]; rfl

theorem impl_sOf {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} (hw : M.IsWeil B.ψ χX χW om)
    (g : UA σ X.J) (h : UA σ W.J) : Impl B.ψ (om (g, h)) (sOf M g h) := by
  have hs := IsUWeilPair.isUSplitting hw
  refine ⟨hs.pres _, fun w Φ hΦ => ?_, fun μ hμ Φ hΦ => hs.unit μ hμ _ Φ hΦ⟩
  have := hs.impl (g, h) (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ) Φ hΦ
  have e : actAB (cA σ) (g, h) (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ) = M.co.e.symm w := by
    change mat g * (mat g⁻¹ * M.co.e.symm w * (mat h⁻¹)ᵀ) * (mat h)ᵀ = _
    have e1 : mat g * mat g⁻¹ = 1 := congrArg mat (mul_inv_cancel g)
    have e2 : mat h * mat h⁻¹ = 1 := congrArg mat (mul_inv_cancel h)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2,
      Matrix.transpose_one, Matrix.mul_one]
  rw [e] at this
  simp only [Darboux.rho, LinearEquiv.apply_symm_apply] at this
  exact this

end Pair

def HtBd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n)
    (W : Spc F E d) (M : Model σ X W), ∃ C : ℝ, 0 ≤ C ∧ ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ∧
      Bd (sOf M g h) m (C * ((ht g : ℝ) * ht h))

def FinInv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ Φ ∈ schA F κ,
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ T s d c, Impl ψ T s → Bd s d c → ∀ w, IntP w → schr ψ (((m₀ * d : ℕ) : AF F) • w) (T Φ) = T Φ

def DerivOK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ w : V F κ × V F κ,
    ∀ Φ ∈ schA F κ, dR ψ w Φ ∈ schA F κ ∧ (∀ x, HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) Φ x) (dR ψ w Φ x) 0) ∧
      ∀ m, Lev m Φ → Lev m (dR ψ w Φ)

def Sob : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ μ, IsHaar μ ∧ ∃ (S : List (List (V F κ × V F κ))) (C : ℝ≥0) (k : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ Θ ∈ schA F κ, Lev m Θ →
      ∀ x, ‖Θ x‖ₑ ^ 2 ≤ C * (m : ℝ≥0∞) ^ k * (S.map fun l => nsq μ (word ψ l Θ)).sum

def TrBd : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℝ, 0 ≤ c ∧ ∀ x : V F κ, ∃ b : V F κ, ‖b‖ ≤ 1 ∧
    ‖x‖ ≤ c * |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b)|

end PositivityTheory.ThKF0.Grow
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.SchwartzDq
section
open Complex GlobalTheory.CompanionTheory.OM.SchDiff
open scoped ContDiff

namespace PositivityTheory.ThKF0

theorem schwartzDq : SchwartzDq := by
  intro V _ _ _ a L f G hG T
  let ph : ℝ × V → ℝ := fun q => -(2 * Real.pi) * (q.1 * L q.2 + q.1 * q.1 * (L a / 2))
  let l : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have h1 := (ContinuousLinearMap.fst ℝ ℝ V).hasTemperateGrowth
  have h2 := (L ∘L ContinuousLinearMap.snd ℝ ℝ V).hasTemperateGrowth
  have hph : Function.HasTemperateGrowth ph :=
    (Function.HasTemperateGrowth.const _).fun_mul ((h1.fun_mul h2).fun_add
      ((h1.fun_mul h1).fun_mul (Function.HasTemperateGrowth.const _)))
  have hA := temperate_exp.comp hph
  let F : ℝ × V → ℂ := fun q => cexp (I * (ph q : ℝ)) * f (q.2 + l q.1)
  have hF : ContDiff ℝ ∞ F := hA.1.mul ((f.smooth ⊤).comp (contDiff_snd.add (l.contDiff.comp contDiff_fst)))
  have hR : ∀ t, ⇑(G t) = fun x => F (t, x) := fun t => by
    funext x
    rw [hG, Lib.hl]
    simp only [F, ph, l, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    congr 2
    push_cast
    ring
  have hd : ∀ x, HasDerivAt (fun t => F (t, x)) (Lib.dop a L f x) 0 := fun x => by
    have e1 : HasDerivAt (fun t : ℝ => ph (t, x)) (-(2 * Real.pi) * L x) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).mul_const (L x)).add
        (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (L a / 2))).const_mul (-(2 * Real.pi)))
      exact this.congr_deriv (by simp)
    have e2 := (e1.ofReal_comp.const_mul I).cexp
    have e3 : HasDerivAt (fun t : ℝ => f (x + l t)) (fderiv ℝ f x a) 0 := by
      have := (f.differentiable (x + l 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (l.hasDerivAt.const_add x)
      exact this.congr_deriv (by simp [l])
    refine (e2.mul e3).congr_deriv ?_
    rw [Lib.dop_apply]
    simp [ph, l]
    ring
  have hD : ∀ v : ℝ, ⇑((v : ℂ) • Lib.dop a L f) = fun x => fderiv ℝ F (0, x) (v, 0) := fun v => by
    funext x
    have e := (hF.differentiable (by simp) (0, x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    have e' : fderiv ℝ F (0, x) (1, 0) = Lib.dop a L f x := e.unique (hd x)
    rw [show ((v, 0) : ℝ × V) = v • (1, 0) by simp, map_smul, e', SchwartzMap.smul_apply, smul_eq_mul, Complex.real_smul]
  have key := hasFDerivAt_family hF 0 (fun k n => bound_mul_translate hA f l 0 k n) G (fun v => (v : ℂ) • Lib.dop a L f) hR hD T
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (T (Lib.dop a L f))) fun v => by simp
  exact key.hasDerivAt.congr_deriv (by simp)

end PositivityTheory.ThKF0
end

