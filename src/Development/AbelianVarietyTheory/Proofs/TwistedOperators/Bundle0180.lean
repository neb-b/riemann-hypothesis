module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.HeckeCharsOfSquare

variable {D : D7}

theorem isHeckeChar_mul {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ * ψ) :=
  ⟨hχ.1.mul hψ.1, fun x => by rw [MonoidHom.mul_apply, hχ.2 x, hψ.2 x, mul_one]⟩

theorem isHeckeChar_inv {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨hχ.1.inv, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

theorem isHeckeChar_div {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ / ψ) := by
  rw [div_eq_mul_inv]; exact isHeckeChar_mul hχ (isHeckeChar_inv hψ)

theorem isHeckeChar_pow {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (n : ℕ) : IsHeckeChar D (χ ^ n) :=
  ⟨hχ.1.pow n, fun x => by rw [MonoidHom.pow_apply, hχ.2 x, one_pow]⟩

theorem resEta_of_mod {χ : (AE D)ˣ →* Circle} {a b : ℕ} (h : ResEta D χ a) (hab : a % 2 = b % 2) : ResEta D χ b := by
  refine ⟨h.1, fun η hη x => ?_⟩
  rw [h.2 η hη x, ← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x, one_pow, one_pow, hab]

theorem resEta_mul {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ * ψ) (a + b) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.mul_apply, hχ.2 η hη x, hψ.2 η hη x, pow_add]⟩

theorem resEta_inv {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) : ResEta D χ⁻¹ a := by
  refine ⟨hχ.1, fun η hη x => ?_⟩
  rw [MonoidHom.inv_apply, hχ.2 η hη x, ← inv_pow]
  have h2 := GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x
  rw [inv_eq_of_mul_eq_one_right (by rw [← sq, h2] : η x * η x = 1)]

theorem resEta_pow {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) (k : ℕ) : ResEta D (χ ^ k) (a * k) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.pow_apply, hχ.2 η hη x, pow_mul]⟩

theorem resEta_div {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ / ψ) (a + b) := by
  rw [div_eq_mul_inv]; exact resEta_mul hχ (resEta_inv hψ)

theorem resEta_of_att {μ η : (AE D)ˣ →* Circle} {a b : ℕ} (ha : ResEta D (Lift.attChr μ η a) a)
    (hb : ResEta D (Lift.attChr μ η b) b) (hab : Odd (a + b)) : ResEta D μ 0 ∧ ResEta D η 1 := by
  rcases Nat.even_or_odd a with hae | hao
  · have hbo : Odd b := (Nat.odd_add'.1 hab).2 hae
    have hna : ¬ Odd a := Nat.not_odd_iff_even.2 hae
    simp only [Lift.attChr, hna, if_false] at ha
    simp only [Lift.attChr, hbo, if_true] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod ha (by rw [Nat.even_iff.1 hae])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := a + b) ?_ (by rw [Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div ha hb
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · exact absurd hab (Nat.not_odd_iff_even.2 (hao.add_odd h))
    have hnb : ¬ Odd b := Nat.not_odd_iff_even.2 hbe
    simp only [Lift.attChr, hao, if_true] at ha
    simp only [Lift.attChr, hnb, if_false] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod hb (by rw [Nat.even_iff.1 hbe])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := b + a) ?_ (by rw [add_comm, Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div hb ha

end GlobalTheory.HeckeCharsOfSquare

namespace GlobalTheory.HeckeCharsOfSquare

end GlobalTheory.HeckeCharsOfSquare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairing
section
open MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_diag_sum_prod_pairing
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hM : ∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) :
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  classical
  set d := Module.finrank ℝ V
  let e : Module.Basis (Fin d) ℝ V := Module.finBasis ℝ V

  have hinj : Function.Injective β.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact hβ q (fun x => by simpa using LinearMap.congr_fun hq x)
  have hsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  choose q hq using fun i : Fin d => hsurj (e.coord i)
  have hqx : ∀ x i, β x (q i) = e.repr x i := by
    intro x i
    have := LinearMap.congr_fun (hq i) x
    simpa using this

  have hexp : ∀ x t, M t x x =
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := by
    intro x t
    conv_lhs => rw [← e.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum,
      Complex.real_smul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  let c : Fin d × Fin d → ℂ := fun p => deriv (fun t => M t (e p.1) (e p.2)) 0
  refine ⟨d * d, fun k => q (finProdFinEquiv.symm k).1, fun k => q (finProdFinEquiv.symm k).2,
    fun k => c (finProdFinEquiv.symm k), fun x => ?_⟩
  have hfun : (fun t => M t x x) = fun t =>
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := funext (hexp x)
  rw [hfun]
  have hd : HasDerivAt (fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j))
      (∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * c (i, j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hM (e i) (e j)).hasDerivAt).const_mul _
  convert hd using 1
  simp only [hqx]
  rw [← Fintype.sum_prod_type']
  rw [← (finProdFinEquiv (m := d) (n := d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkew
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatrixCoeffDeriv

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

private theorem measure_fundamentalDomain_ratL_lt_top {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := hμ
  obtain ⟨-, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have := hsc
  have := hdisc
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : MeasurableConstVAdd (ratL W V) (WO V W) :=
    ⟨fun γ => (continuous_const_add (γ : WO V W)).measurable⟩
  have : VAddInvariantMeasure (ratL W V) (WO V W) μ :=
    ⟨fun γ _ hs => Measure.measure_preimage_of_map_eq_self
      (Measure.IsAddLeftInvariant.map_add_left_eq_self (γ : WO V W))
      (continuous_const_add (γ : WO V W)).measurable.aemeasurable hs.nullMeasurableSet⟩
  have : Countable (ratL W V) :=
    (TopologicalSpace.separableSpace_iff_countable (α := ratL W V)).1 inferInstance
  have hsub : 𝓕 ⊆ ⋃ γ : ratL W V, ((γ +ᵥ ·) '' K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγK⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨⟨-γ, neg_mem hγ⟩, ⟨γ + x, hγK, ?_⟩, hx⟩
    show -γ + (γ + x) = x
    abel
  calc μ 𝓕 ≤ μ (⋃ γ : ratL W V, ((γ +ᵥ ·) '' K ∩ 𝓕)) := measure_mono hsub
    _ ≤ ∑' γ : ratL W V, μ ((γ +ᵥ ·) '' K ∩ 𝓕) := measure_iUnion_le _
    _ = μ K := (h𝓕.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem hasDerivAt_integral_line (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W}
    (hL : IsRealDir W V L) {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f g : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W g) :
    HasDerivAt (fun t : ℝ => ∫ x in 𝓕, heisO ψ V W (L t) f x * (starRingEnd ℂ) (g x) ∂μ)
      (∫ x in 𝓕, dLine ψ V W L f x * (starRingEnd ℂ) (g x) ∂μ) 0 := by
  have := hμ
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (measure_fundamentalDomain_ratL_lt_top hμ h𝓕).ne
  have hd : IsThetaFunO ψ V W (dLine ψ V W L f) := theta_dLine hθ hψ hL h
  obtain ⟨C, hC⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := V) (W := W) hψ _ hd).2.1
  obtain ⟨C₀, hC₀⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := V) (W := W) hψ _ h).2.1
  have hgi : Integrable g (μ.restrict 𝓕) :=
    ((GlobalTheory.ThetaSquare.squareIntegrable (V := V) (W := W) hψ _ h').2.2 μ 𝓕 hμ h𝓕).integrable one_le_two
  have hcg : Continuous fun x => (starRingEnd ℂ) (g x) := Complex.continuous_conj.comp h'.cont
  have hc : ∀ k : WO V W → ℂ, IsThetaFunO ψ V W k → ∀ t : ℝ,
      Continuous fun x => heisO ψ V W (L t) k x * (starRingEnd ℂ) (g x) :=
    fun k hk t => (theta_heisO_real hθ hψ (hL.2 t) hk).cont.mul hcg
  have hb : ∀ (k : WO V W → ℂ) (B : ℝ), (∀ y, ‖k y‖ ≤ B) → ∀ (t : ℝ) (x : WO V W),
      ‖heisO ψ V W (L t) k x * (starRingEnd ℂ) (g x)‖ ≤ B * ‖g x‖ := by
    intro k B hk t x
    rw [norm_mul, GlobalTheory.ThetaSquare.norm_heisO hψ, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hk _) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
    (F := fun t x => heisO ψ V W (L t) f x * (starRingEnd ℂ) (g x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) x * (starRingEnd ℂ) (g x))
    (bound := fun x => C * ‖g x‖) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hc f h t).aestronglyMeasurable)
    ((hgi.norm.const_mul C₀).mono' (hc f h 0).aestronglyMeasurable (ae_of_all _ (hb f C₀ hC₀ 0)))
    (hc _ hd 0).aestronglyMeasurable
    (ae_of_all _ fun x t _ => hb _ C hC t x) (hgi.norm.const_mul C)
    (ae_of_all _ fun x t _ => (hasDerivAt_heisO hθ hψ hL h x t).mul_const _)
  have h0 : ∀ (k : WO V W → ℂ) (x : WO V W), heisO ψ V W (L 0) k x = k x := by
    intro k x
    simp only [map_zero, heisO, GlobalTheory.ThetaSquare.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  simpa only [h0] using key.2

theorem hasDerivAt_ipO_and_skew : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) g) (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g) 0 ∧ ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g = -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  intro D ψ θ S T μ 𝓕 hψ hθ hcov f g hf hg τ z
  obtain ⟨hμ, h𝓕, -⟩ := hcov
  refine ⟨?_, ((GlobalTheory.ThetaSquare.derSkew hψ hθ) τ z).2.2 μ 𝓕 hμ h𝓕 f g hf hg⟩
  rw [dRho_eq_dLine]
  exact hasDerivAt_integral_line hψ hθ (isRealDir_lineAt hθ τ z) hμ h𝓕 hf hg

end GlobalTheory.MatrixCoeffDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasProdLocalTwistedLFactorDivUnitaryLocalFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem abs_quadTerm_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) {i : ℕ} (hi : 2 ≤ i) :
    ‖-quadTerm D v i‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm v
  have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp
  rw [norm_neg, Real.norm_eq_abs, quadTerm, abs_div, abs_pow, abs_pow, hs, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)), Real.rpow_neg (by positivity),
    Real.rpow_two]
  have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i :=
    pow_le_pow_right₀ hN.le hi
  rw [one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast h2)

theorem hasProd_dLoc (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => dLoc D v.1) (dOff D Sb) ∧ dOff D Sb ≠ 0 := by
  have ht := D.R.rank_add_five_le
  set f : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV → ℝ :=
    fun p => -quadTerm D p.1.1 p.2.1 with hf
  have hsum0 := summable_rpow (K := D.host.F) (Sb : Set _) (σ := 2) (by norm_num)
  have hsum1 : Summable fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV =>
      ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 : ℝ) := by
    refine summable_mul_of_summable_norm (f := fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ))) (g := fun _ : Finset.Ioc D.R.t D.R.nV => (1 : ℝ)) ?_ ?_
    · refine hsum0.congr fun v => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact Summable.of_finite
  have hsum : Summable fun p => ‖f p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hsum1
    rw [mul_one]
    have := (Finset.mem_Ioc.1 p.2.2).1
    exact abs_quadTerm_le D p.1.1 (by omega)
  have hne : ∀ p, 1 + f p ≠ 0 := fun p => by
    have h1 := abs_quadTerm_le D p.1.1 (i := p.2.1) (by have := (Finset.mem_Ioc.1 p.2.2).1; omega)
    have hN : (1 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm p.1.1
    have h2 : ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hN (by norm_num)
    intro h0
    have : f p = -1 := by linarith
    rw [hf] at this
    simp only at this
    rw [this, norm_neg, norm_one] at h1
    linarith
  have hm := multipliable_one_add_of_summable hsum
  have hz := tprod_one_add_ne_zero_of_summable hne hsum
  have hinv : HasProd (fun p => (1 + f p)⁻¹) (∏' p, (1 + f p))⁻¹ := hm.hasProd.inv₀ hz
  have e1 : (fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV => (1 + f p)⁻¹) =
      fun p => (1 - quadTerm D p.1.1 p.2.1)⁻¹ := by
    funext p; rw [hf]; ring_nf
  rw [e1] at hinv
  have hd : dOff D Sb = (∏' p, (1 + f p))⁻¹ := hinv.tprod_eq
  refine ⟨?_, hd ▸ inv_ne_zero hz⟩
  rw [hd]
  refine hinv.prod_fiberwise fun v => ?_
  have := hasProd_fintype (fun c : Finset.Ioc D.R.t D.R.nV => (1 - quadTerm D v.1 c.1)⁻¹)
  rw [Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) (fun i => (1 - quadTerm D v.1 i)⁻¹)] at this
  exact this

theorem hasProd_LvTw_div_dLoc : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  intro D Sb B χ h
  have h1 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2)) :=
    hasProd_Lv h
  obtain ⟨h2, h3⟩ := hasProd_dLoc D Sb
  have h4 := (h2.map Complex.ofRealHom Complex.continuous_ofReal).inv₀
    (by simpa using h3 : Complex.ofRealHom (dOff D Sb) ≠ 0)
  have h5 := h1.mul h4
  simpa [div_eq_mul_inv, Function.comp_def] using h5

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDu
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem sumOp_vec_zero {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) : sumOp W A B 0 = 0 := by
  unfold sumOp; simp

theorem form_translate_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {Λ : Submodule R X}
    (hΛ : SelfDual γ Λ) {s : M} (hs : Fixes W Λ s) (e : M →ₗ[ℂ] ℂ) (he : ∀ a ∈ Λ, ∀ v, e (W a v) = e v) (x : X) :
    e (W x s) = if x ∈ Λ then e s else 0 := by
  split_ifs with hx
  · rw [hs x hx]
  · obtain ⟨a, ha, hne⟩ : ∃ a ∈ Λ, γ x a ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hx ((hΛ x).2 hc)
    have h1 : e (W x s) = γ a x * e (W x s) := by
      conv_lhs => rw [← he a ha (W x s)]
      rw [h.comm a x s, hs a ha, map_smul, smul_eq_mul]
    have h2 : γ a x ≠ 1 := by
      rw [h.swap x a]
      intro h3
      exact hne (inv_eq_one.1 h3)
    have h3 : (1 - γ a x) * e (W x s) = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm h2))

theorem sumOp_vacuum_lift : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs0 hs hspan Λ' hΛ' hidx
  obtain ⟨hidx', hss⟩ := sumOp_sumOp_eq_idx_smul h Λ Λ' hΛ hΛ' hidx
  obtain ⟨⟨n, f, hf, ht⟩, hfix, -⟩ := (sumOp_transversal h Λ Λ' hΛ').2.1 hidx
  have hs'fix : Fixes W Λ' (sumOp W Λ Λ' s) := hfix s hs
  have hback := hss s hs
  have hidxC : (idx Λ Λ' : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hne : sumOp W Λ Λ' s ≠ 0 := by
    intro h0
    rw [h0, sumOp_vec_zero] at hback
    exact hs0 ((smul_eq_zero.1 hback.symm).resolve_left hidxC)
  have hidx2 : idx Λ' Λ ≠ 0 := by rw [hidx']; exact hidx
  obtain ⟨⟨m, g, hg, hgt⟩, -, -⟩ := (sumOp_transversal h Λ' Λ hΛ).2.1 hidx2
  have hsum := ((sumOp_transversal h Λ' Λ hΛ).1 _ hs'fix (Fin m) g hg hgt).1
  have hsE : s = ((idx Λ Λ' : ℂ))⁻¹ • ∑ i, W (g i) (sumOp W Λ Λ' s) := by
    rw [← hsum, hback, smul_smul, inv_mul_cancel₀ hidxC, one_smul]
  have hmem : ∀ x, W x s ∈ Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [congrArg (W x) hsE, map_smul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [h.comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hspan' : Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine ⟨⟨hne, hs'fix, hspan'⟩, fun e he1 he v hv => ?_⟩
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergVacuum_unique_of_selfDual h Λ' hΛ' _ hne hs'fix hspan' v hv
  have hes' : e (sumOp W Λ Λ' s) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [((sumOp_transversal h Λ Λ' hΛ').1 s hs (Fin n) f hf ht).1, map_sum]
    simp only [form_translate_vacuum h hΛ hs e he, he1]
    obtain ⟨i0, hi0, huniq⟩ := ht 0 Λ'.zero_mem
    rw [Finset.sum_eq_single i0]
    · rw [if_pos (by simpa using hi0)]
    · intro j _ hj
      rw [if_neg]
      intro hjΛ
      exact hj (huniq j (by simpa using hjΛ))
    · simp
  rw [map_smul, hes', smul_eq_mul, mul_one]

end GlobalTheory.SphTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LamInert

theorem lam_qV_inert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  intro D lam hl v w hw
  have hmap : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = w.asIdeal := hw
  have hfix : ∀ x : 𝓞 D.host.F, GlobalTheory.FinWeil.sgO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := fun x => by
    apply RingOfIntegers.coe_injective
    refine (GlobalTheory.FinWeil.coe_sgO D _).trans ?_
    exact (D.host.conjE_mem_hostF_iff _).1 (by
      change ((x : D.host.F) : D.host.E) ∈ _
      exact (x : D.host.F).2)
  have hstab : ∀ r ∈ w.asIdeal, GlobalTheory.FinWeil.sgO D r ∈ w.asIdeal := by
    rw [← hmap]
    have : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤
        (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal).comap (GlobalTheory.FinWeil.sgO D) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hfix]
      exact Ideal.mem_map_of_mem _ hx
    exact fun r hr => this hr
  have hfin : Finite (𝓞 D.host.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have h1 := ((hl.2 w.asIdeal w.isMaximal hfin).2 hstab).1
  have hcard : Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = qV D.host.E w := by
    change _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : qV D.host.E w = qV D.host.F v ^ 2 :=
    GlobalTheory.LFun.InertChart.absNorm_eq (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hw
  rw [hcard, hsq] at h1
  rw [hsq, h1]
  congr 1
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.LamInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_levelIdempotentProduct_and_centralProduct : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  first | exact @GlobalTheory.LevRange.ranges | exact GlobalTheory.LevRange.ranges | (intros; apply GlobalTheory.LevRange.ranges <;> assumption)
end

