module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import ReciprocityTheory.AdeleApproximation.AdeleIntA
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulFinsum

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_eq {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h x = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) x) (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem actO_actO {S T : HSp D} (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  rw [actO_eq, actO_eq, actO_eq, _root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_one {S T : HSp D} (x : WO S T) : actO S T 1 1 x = x := by
  rw [actO_eq, inv_one, mt_one', mt_one', Matrix.one_mul, Matrix.mul_one]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  rw [actO_eq, actO_eq, actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_eq, Matrix.mul_zero, Matrix.zero_mul]
  | succ k ih => rw [succ_nsmul, actO_add, ih, succ_nsmul]

theorem isHalf_mul_mul {e : AE D} {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) (x : Matrix (Fin b) (Fin c) (AE D))
    (N : Matrix (Fin c) (Fin c) (AE D)) (hx : IsHalf e x) : IsHalf e (M * x * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hx k l]
  ring

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
      rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
    rw [← this]
    exact isHalf_mul_mul _ _ _ hx
  · intro hx
    exact isHalf_mul_mul _ _ _ hx

def actPull {S T : HSp D} (p : GA D S × GA D T) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun t => Φ (actO S T p.1⁻¹ p.2⁻¹ t)

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Psi

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_norm (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ‖ψ a‖ = 1 := hψ.1.2.1 a

theorem psi_ne (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := psi_norm hψ a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem psi_cont (hψ : IsStdChar D ψ (-1)) : Continuous ψ := hψ.1.1

end Psi

section Cont

variable (S T : HSp D)

theorem cont_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap _

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := Formalism.IndefR.PHeisTh.cA_smul

theorem cont_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem cont_hO : Continuous fun p : MO S T × MO S T => hO S T p.1 p.2 := by
  have hcA : Continuous (cA D) := cont_cA
  delta hO
  fun_prop

theorem cont_symplO : Continuous fun p : MO S T × MO S T => symplO S T p.1 p.2 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := cont_trace
  have hh := cont_hO S T
  delta symplO
  first
    | exact ht.comp (continuous_const.mul hh)
    | fun_prop

theorem cont_symplO_left (w : MO S T) : Continuous fun z : MO S T => symplO S T z w := by
  have h : Continuous (Function.uncurry (symplO S T)) := cont_symplO S T
  exact h.uncurry_right w

theorem cont_symplOH_left (w : MO S T) : Continuous fun z : MO S T => symplOH S T z w := by
  delta symplOH
  exact continuous_const.mul (cont_symplO_left S T w)

end Cont

section Per

variable (S T : HSp D)

end Per

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

theorem cont_heis (hψ : IsStdChar D ψ (-1)) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (v : MO S T) :
    Continuous (heisO ψ S T v f) := by
  delta heisO
  exact ((psi_cont hψ).comp (cont_symplOH_left S T v)).mul (hf.3.comp (continuous_add_const v))

theorem theta_zero : IsThetaFunO ψ S T 0 := by
  exact ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext z; simp [heisO]⟩, continuous_zero,
    fun k L _ _ _ => contDiff_const⟩

theorem theta_add {f g : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  obtain ⟨hq2, ⟨U2, hU2, hl2⟩, hc2, hs2⟩ := hg
  refine ⟨fun γ w => ?_, ⟨U1 ⊓ U2, ?_, fun u hu h0 => ?_⟩, hc1.add hc2,
    fun k L hL h0 w => (hs1 k L hL h0 w).add (hs2 k L hL h0 w)⟩
  · simp only [Pi.add_apply, hq1 γ w, hq2 γ w, mul_add]
  · rw [AddSubgroup.coe_inf]
    exact hU1.inter hU2
  · have e1 := hl1 u hu.1 h0
    have e2 := hl2 u hu.2 h0
    funext z
    have z1 := congrFun e1 z
    have z2 := congrFun e2 z
    simp only [heisO, Pi.add_apply, Pi.zero_apply] at z1 z2 ⊢
    rw [mul_add, z1, z2]

theorem theta_smul (c : ℂ) {f : MO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
  obtain ⟨hq1, ⟨U1, hU1, hl1⟩, hc1, hs1⟩ := hf
  refine ⟨fun γ w => ?_, ⟨U1, hU1, fun u hu h0 => ?_⟩, hc1.const_smul c,
    fun k L hL h0 w => (hs1 k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hq1 γ w]
    ring
  · have e1 := hl1 u hu h0
    funext z
    have z1 := congrFun e1 z
    simp only [heisO, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at z1 ⊢
    rw [mul_left_comm, z1]

end Theta

section Svn

variable {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

end Svn

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.NormNatCastLtOne
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter

namespace Formalism.IndefR.Fin.U1

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 := (norm_le_one_iff_int v _).mpr (natCast_mem _ m)

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  rw [← map_natCast (algebraMap F (v.adicCompletion F)) m]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hm)

theorem natCast_apply' (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) : (N : Af F) v = (N : v.adicCompletion F) := by
  first
  | rfl
  | simp

theorem natCast_mul_apply' (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply' N v]
  rfl

theorem norm_natCast_lt_one' (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
  rw [Valued.toNormedField.norm_lt_one_iff]
  have h1 : ((c : v.adicCompletion F)) = ((algebraMap (𝓞 F) F (c : 𝓞 F) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    first
    | exact (map_natCast (algebraMap F (v.adicCompletion F)) c).symm
    | norm_cast
    | rfl
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem _).mpr hmem

theorem finNhd (U : Set (Af F)) (hU : U ∈ 𝓝 (0 : Af F)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) → (N : Af F) * z ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one' v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩
  have hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    rw [natCast_mul_apply']
    exact mul_mem (natCast_mem _ _) (hz v)
  have hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hx]
  apply hIt
  intro v hv
  apply hεt
  show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v
  rw [natCast_mul_apply', norm_mul, Nat.cast_pow, norm_pow]
  have hz1 : ‖z v‖ ≤ 1 := (norm_le_one_iff_int v _).2 (hz v)
  calc ‖(c : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hz1 (pow_nonneg (norm_nonneg _) _)
    _ < ε v := by rw [mul_one]; exact hk v hv

theorem int_of_le (y : Af F) (N M : ℕ) (hN : N ≠ 0)
    (hy : ∀ v, ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖) :
    ∃ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) ∧ y = (N : Af F) * z := by
  refine ⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩
  · rw [← norm_le_one_iff_int]
    show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1
    have hN0 : 0 < ‖(N : v.adicCompletion F)‖ := norm_pos_iff.2 (nat_ne_zero_fin v hN)
    rw [map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]
    calc ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖ := hy v
      _ ≤ ‖(N : v.adicCompletion F)‖ * 1 := mul_le_mul_of_nonneg_left (norm_nat_le_one v M) hN0.le
      _ = ‖(N : v.adicCompletion F)‖ := mul_one _
  · rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]

end Formalism.IndefR.Fin.U1

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualASt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT))

def PlaceLatDualIii (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT))

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v

def PlaceLatDualV (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceLatDualVi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT

end Formalism.IndefR.Fin

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceHeis
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def heisL (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by
    funext x
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext x
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem heisL_apply (w : WO S T) (f : WO S T → ℂ) : heisL ψ S T w f = heisO ψ S T w f := rfl

def halfSub (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf e u}
  add_mem' {a b} ha hb := fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by rw [Matrix.zero_apply, mul_zero]
  neg_mem' {a} ha := fun i j => by rw [Matrix.neg_apply, mul_neg, ha i j]

theorem heisO_heisO (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [symplOH_add_left S T x w w', symplOH_add_right S T x w w', AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc x w w']
  ring

theorem psi_ne_zero (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem symplO_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplO S T x y = 0 := by
  have hz : ∀ a b c d, incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a = 0 := by
    intro a b c d
    rw [← hy c b, ← hx d a, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  simp [symplO, hO, hz]

theorem symplOH_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  rw [symplOH, symplO_half S T he hx hy, mul_zero]

theorem heisL_add_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y := by
  ext1 f
  rw [Module.End.mul_apply, heisL_apply, heisL_apply, heisL_apply, heisO_heisO, symplOH_half S T he hx hy,
    AddChar.map_zero_eq_one, one_smul]

theorem heisL_comm (x y : WO S T) :
    heisL ψ S T x * heisL ψ S T y = ψ (symplO S T x y) • (heisL ψ S T y * heisL ψ S T x) := by
  ext1 f
  simp only [Module.End.mul_apply, LinearMap.smul_apply, heisL_apply]
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm y x, symplOH_swap S T x y, ← symplOH_two S T x y,
    ← AddChar.map_add_eq_mul, show symplOH S T x y + symplOH S T x y + -symplOH S T x y = symplOH S T x y by abel]

theorem cA_half_orth {e : AE D} (he : e * cA D e = 0) : cA D e * cA D (cA D e) = 0 := by
  rw [cA_cA, mul_comm, he]

end Formalism.IndefR.Fin

end
end

