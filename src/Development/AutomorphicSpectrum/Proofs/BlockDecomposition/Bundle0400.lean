module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.UnipGLMemAdelicBorel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import GroundTheory.LocalFields.UnitsBasic

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacter
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCountG.LefDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

theorem trace_dualT (E : KMod n) (S : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      LinearMap.trace ℂ E.V (S : E.V →ₗ[ℂ] E.V) := by
  let e : Module.Dual ℂ E.V ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  have h : (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      e.conj (Module.Dual.transpose (R := ℂ) (S : E.V →ₗ[ℂ] E.V)) := by
    ext φ x
    simp [e, dualT, LinearEquiv.conj_apply, Module.Dual.transpose_apply]
  rw [h, LinearMap.trace_conj', LinearMap.trace_transpose']

theorem weylChar_conj_arg (lam : Fin n → ℤ) (u : Fin n → ℂ) :
    weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀]

theorem conj_eq_inv (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) (a : Fin n) :
    z a ≠ 0 ∧ conj (z a) = (z a)⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.1 k.2
  rw [hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at h
  have ha := congrFun (congrFun h a) a
  rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] at ha
  have h1 : conj (z a) * z a = 1 := ha
  have h0 : z a ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact ⟨h0, eq_inv_of_mul_eq_one_left h1⟩

theorem trace_dualT_inv (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z)
    (hinj : Function.Injective (fun a => z a ^ 2)) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  have hz := conj_eq_inv k z hk
  have hk' : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = diagonal (fun a => (z a)⁻¹) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, hk, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    exact (hz a).2
  have hinj' : Function.Injective (fun a => (z a)⁻¹ ^ 2) := fun a b h => by
    apply hinj
    simpa [inv_pow] using h
  obtain ⟨-, -, h3⟩ := hT
  obtain ⟨-, h2⟩ := h3 k⁻¹ (fun a => (z a)⁻¹) hk' hinj'
  beta_reduce at h2
  rw [trace_dualT, h2]
  have hw : (fun a => (z a)⁻¹ ^ 2) = fun a => conj (z a ^ 2) := by
    funext a
    rw [map_pow, (hz a).2]
  congr 1
  · simp_rw [inv_div_inv]
    exact Finset.prod_comm
  · rw [hw, weylChar_conj_arg, Complex.conj_conj]

end GlobalTheory.CompanionTheory.RealCountG.LefDual
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundConstantTerm
section
noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An PositivityTheory.Rg.Rs.ctstepglue

namespace GlobalTheory.CompanionTheory.Conc

theorem ubnd_ctn {K : Type} [Field K] [NumberField K] {n : ℕ} {ι : Type}
    {r : ℕ} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (h : UBnd f m) :
    UBnd (fun i => An.ctn r (f i)) m := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨D, hD, hFD⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  set ω' := (fun p : (UPos n r → NumberField.AdeleRing (𝓞 K) K) × AdelicGLn.AdelicGL K n => unipGL p.1 * p.2) '' (D ×ˢ ω)
  have hω' : IsCompact ω' :=
    (hD.prod hω).image ((continuous_unipGL.comp continuous_fst).mul continuous_snd)
  have hω'B : ω' ⊆ (adelicBorel (K := K) (n := n) : Set _) := by
    rintro _ ⟨⟨X, b⟩, ⟨hX, hb⟩, rfl⟩
    exact mul_mem (unipGL_mem_adelicBorel r X) (hωB hb)
  obtain ⟨C, hC⟩ := h ω' hω' hω'B t₀ Q hQ
  refine ⟨max C 0, fun i b hb x hx q hq => ?_⟩
  refine norm_ctn_le (f i) hD hFD _ (by positivity) fun X hX => ?_
  have := hC i (unipGL X * b) ⟨(X, b), ⟨hX, hb⟩, rfl⟩ x hx q hq
  rw [← mul_assoc, ← mul_assoc]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem ubnd_ctn_step : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r D : ℕ) (κ' κ : ℝ) (p : ι → ℂ[X]),
  0 < r → r < n → UFam f → UBnd f m → κ' < κ →
  (∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (f i) (p i) ∧ ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') →
  UBnd (fun i => An.ctn r (f i)) (Function.update m r κ) := by
  intro K _ _ n ι f m r D κ' κ pf hr hrn hf hB hκ hpf ω hω hωB t₀ Q hQ
  obtain ⟨C₁, hC₁⟩ := ubnd_ctn (r := r) hB ω hω hωB t₀ Q hQ
  obtain ⟨C₂, hC₂0, hC₂⟩ := _root_.GlobalTheory.CompanionTheory.LinRec.uniformRecBound D κ' κ hκ
  set E : ℝ := Real.exp (|m r| * (|t₀| + 1 + D)) with hE
  refine ⟨C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)), ?_⟩
  intro a b hb x hx q hq
  obtain ⟨hp, hdD, hK, hroot⟩ := hpf a
  set p := pf a with hpdef
  set φ := f a with hφdef
  set d := p.natDegree with hd
  set S : ℝ := ∑ r' ∈ (Finset.range n).erase r, m r' * sr x r' with hS
  have hrmem : r ∈ Finset.range n := Finset.mem_range.2 hrn
  have hsum : ∀ (f : ℕ → ℝ) (y : Fin n → ℝ), (∀ r' ≠ r, f r' = m r') → (∀ r' ≠ r, sr y r' = sr x r') →
      ∑ r' ∈ Finset.range n, f r' * sr y r' = f r * sr y r + S := by
    intro f y hf hy
    rw [← Finset.add_sum_erase _ _ hrmem, hS]
    congr 1
    refine Finset.sum_congr rfl fun r' h' => ?_
    rw [hf r' (Finset.ne_of_mem_erase h'), hy r' (Finset.ne_of_mem_erase h')]
  have h0 : 0 ≤ sr x r + t₀ := by linarith [hx r]
  set i : ℕ := ⌊sr x r + t₀⌋₊ with hi
  have hi1 : (i : ℝ) ≤ sr x r + t₀ := Nat.floor_le h0
  have hi2 : sr x r + t₀ < i + 1 := Nat.lt_floor_add_one _
  set x' : Fin n → ℝ := shift r x (-(i : ℝ)) with hx'
  set g₀ : AdelicGLn.AdelicGL K n := b * tor K x' * q with hg₀
  set u : ℕ → ℂ := fun k => ctn r φ (aR K n r k * g₀) with hu
  have hrecu : ∀ k, ∑ j ∈ Finset.range (d + 1), p.coeff j * u (k + j) = 0 := by
    intro k
    have := hK (aR K n r k * g₀)
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu, ← mul_assoc, aR_mul]
    congr 4
    push_cast; ring

  have hmove : ∀ (t : ℝ) (h : AdelicGLn.AdelicGL K n), ctn r φ (aR K n r t * (b * h)) = ctn r φ (b * (aR K n r t * h)) := by
    intro t h
    obtain ⟨X, hX⟩ := borel_aR (r := r) (hωB hb) t
    have : aR K n r t * b = unipGL (-X) * (b * aR K n r t) := by
      rw [hX, ← mul_assoc, ← unipGL_add, neg_add_cancel, unipGL_zero, one_mul]
    rw [← mul_assoc, this, mul_assoc, ctn_unipGL_mul (hf.left a), ← mul_assoc]
  set M : ℝ := max C₁ 0 * E * Real.exp S with hM
  have hM0 : 0 ≤ M := by positivity
  have hinit : ∀ j < d, ‖u j‖ ≤ M := by
    intro j hj
    have e1 : u j = ctn r φ (b * tor K (shift r x ((j : ℝ) - i)) * q) := by
      simp only [hu, hg₀, mul_assoc]
      rw [hmove, ← mul_assoc (aR K n r j), ← tor_shift, hx',
        show shift r (shift r x (-(i : ℝ))) (j : ℝ) = shift r x ((j : ℝ) - i) from by
          funext l; simp only [shift]; split_ifs <;> ring]
    have hsr : ∀ r', sr (shift r x ((j : ℝ) - i)) r' = sr x r' + if r' = r then (j : ℝ) - i else 0 :=
      sr_shift hr hrn x _
    have hx2 : ∀ r', -t₀ ≤ sr (shift r x ((j : ℝ) - i)) r' := by
      intro r'
      rw [hsr]
      split_ifs with h
      · subst h; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      · simpa using hx r'
    have hb1 := hC₁ a b hb _ hx2 q hq
    rw [e1]
    refine hb1.trans ?_
    rw [hsum m _ (fun _ _ => rfl) (fun r' h => by rw [hsr, if_neg h, add_zero]), hsr, if_pos rfl,
      Real.exp_add, hM, ← mul_assoc]
    have hjd : (j : ℝ) ≤ D := by exact_mod_cast (hj.le.trans hdD)
    have hv : |sr x r + ((j : ℝ) - i)| ≤ |t₀| + 1 + D := by
      rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
    have hexp : Real.exp (m r * (sr x r + ((j : ℝ) - i))) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.2
      calc m r * (sr x r + ((j : ℝ) - i)) ≤ |m r * (sr x r + ((j : ℝ) - i))| := le_abs_self _
        _ = |m r| * |sr x r + ((j : ℝ) - i)| := abs_mul _ _
        _ ≤ |m r| * (|t₀| + 1 + D) := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    have hC : C₁ ≤ max C₁ 0 := le_max_left _ _
    gcongr
  have hmain := hC₂ p hp hdD hroot u M hrecu hinit hM0 i
  have heq : ctn r φ (b * tor K x * q) = u i := by
    have : x = shift r x' (i : ℝ) := by
      funext l; simp only [hx', shift]; split_ifs <;> ring
    simp only [hu, hg₀]
    conv_lhs => rw [this, tor_shift]
    rw [mul_assoc b (tor K x') q, hmove]
    simp only [mul_assoc]
  show ‖ctn r φ (b * tor K x * q)‖ ≤ _
  rw [heq]
  refine hmain.trans ?_
  rw [hsum (Function.update m r κ) x (fun r' h => Function.update_of_ne h _ _) (fun _ _ => rfl),
    Function.update_self, Real.exp_add, hM]
  have hk : Real.exp (κ * i) ≤ Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : |(i : ℝ) - sr x r| ≤ |t₀| + 1 := by
      rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
    have := mul_le_mul_of_nonneg_left this (abs_nonneg κ)
    have h2 : κ * ((i : ℝ) - sr x r) ≤ |κ| * |(i : ℝ) - sr x r| := by
      rw [← abs_mul]; exact le_abs_self _
    nlinarith
  have hE0 : 0 ≤ max C₁ 0 * E := by positivity
  calc C₂ * Real.exp (κ * i) * (max C₁ 0 * E * Real.exp S)
      ≤ C₂ * (Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1))) * (max C₁ 0 * E * Real.exp S) := by
        gcongr
    _ = C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)) * (Real.exp (κ * sr x r) * Real.exp S) := by ring

end GlobalTheory.CompanionTheory.Conc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSiegelSet
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.TailU

open GlobalTheory.CompanionTheory.SlabGlue An

theorem isCompact_box {K : Type} [Field K] [NumberField K] {n : ℕ} {ω : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (x : Fin n → ℝ) :
    IsCompact {g : AdelicGLn.AdelicGL K n | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧
      ∃ k ∈ maxCompact (K := K) (n := n), g = b * tor K (x + y) * k} := by
  have hY : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-(n : ℝ)) n) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hc : Continuous fun p : AdelicGLn.AdelicGL K n × (Fin n → ℝ) × AdelicGLn.AdelicGL K n =>
      p.1 * tor K (x + p.2.1) * p.2.2 :=
    (continuous_fst.mul (JSqIntGlue.continuous_tor.comp
      (continuous_const.add (continuous_fst.comp continuous_snd)))).mul
      (continuous_snd.comp continuous_snd)
  convert (hω.prod (hY.prod (isCompact_maxCompact (K := K) (n := n)))).image hc using 1
  ext g
  constructor
  · rintro ⟨b, hb, y, hy, k, hk, rfl⟩
    exact ⟨(b, y, k), ⟨hb, fun i _ => abs_le.1 (hy i), hk⟩, rfl⟩
  · rintro ⟨⟨b, y, k⟩, ⟨hb, hy, hk⟩, rfl⟩
    exact ⟨b, hb, y, fun i => abs_le.2 (hy i trivial), k, hk, rfl⟩

theorem tail_lib (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (AdelicGLn.AdelicGL K n))
    [μ.IsHaarMeasure] (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hB : UBnd f κ) (hκ : ∀ r, 0 < r → r < n → κ r < An.rho K n r)
    (ω : Set (AdelicGLn.AdelicGL K n)) (hω : IsCompact ω)
    (hωB : ω ⊆ (adelicBorel (K := K) (n := n) : Set _)) (t₀ : ℝ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  obtain ⟨Cv, hCv⟩ := boxvol_holds K n μ ω hω hωB
  obtain ⟨C, hC⟩ := hB ω hω hωB (|t₀| + 2 * n) (maxCompact (K := K) (n := n) : Set _)
    isCompact_maxCompact
  let box : (Fin n → ℝ) → Set (AdelicGLn.AdelicGL K n) := fun x =>
    {g | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧ ∃ k ∈ maxCompact (K := K) (n := n),
      g = b * tor K (x + y) * k}
  let X : (Fin (n - 1) → ℕ) → Fin n → ℝ := fun s => part n fun j => -t₀ + s j
  let a : Fin (n - 1) → ℝ := fun j => 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))
  let E : ℝ := ∑ r ∈ Finset.range n, |κ r| * (2 * n)
  let D : ℝ := (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j)
  have ha : ∀ j, a j < 0 := by
    intro j
    have hj := j.2
    have := hκ ((j : ℕ) + 1) (by omega) (by omega)
    show 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)) < 0
    linarith
  have hXs : ∀ s (j : Fin (n - 1)), sr (X s) ((j : ℕ) + 1) = -t₀ + s j := fun s j => sr_part _ j

  have hcover : slab ω t₀ ⊆ ⋃ s, box (X s) := by
    rintro g ⟨b, hb, x, hx, hlast, k, hk, rfl⟩
    let s : Fin (n - 1) → ℕ := fun j => ⌊sr x ((j : ℕ) + 1) + t₀⌋₊
    refine Set.mem_iUnion.2 ⟨s, b, hb, x - X s, ?_, k, hk, ?_⟩
    · refine abs_y_le _ ?_ ?_
      · intro i hi
        have : X s i = 0 := part_last _ i hi
        simpa [this] using hlast i hi
      · intro j
        have e : sr x ((j : ℕ) + 1) = sr (X s) ((j : ℕ) + 1) + sr (x - X s) ((j : ℕ) + 1) := by
          rw [← sr_add, add_sub_cancel]
        rw [hXs] at e
        have h0 : 0 ≤ sr x ((j : ℕ) + 1) + t₀ := by
          have := hx ((j : ℕ) + 1)
          linarith
        have h1 : ((s j : ℕ) : ℝ) ≤ sr x ((j : ℕ) + 1) + t₀ := Nat.floor_le h0
        have h2 : sr x ((j : ℕ) + 1) + t₀ < (s j : ℕ) + 1 := Nat.lt_floor_add_one _
        constructor <;> linarith
    · rw [add_sub_cancel]

  have hbox : ∀ i s, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) := by
    intro i s
    let S : ℝ := ∑ r ∈ Finset.range n, κ r * sr (X s) r
    let W : ℝ := max C 0 * Real.exp E * Real.exp S
    have hW0 : 0 ≤ W := by positivity
    have hnorm : ∀ g ∈ box (X s), ‖f i g‖ₑ ^ 2 ≤ ENNReal.ofReal (W ^ 2) := by
      rintro g ⟨b, hb, y, hy, k, hk, rfl⟩
      have hsr : ∀ r, -(|t₀| + 2 * n) ≤ sr (X s + y) r := by
        intro r
        by_cases hr : 0 < r ∧ r < n
        · rw [sr_add]
          have h1 : sr (X s) r = -t₀ + s ⟨r - 1, by omega⟩ := by
            have := hXs s ⟨r - 1, by omega⟩
            simp only at this
            rwa [Nat.sub_add_cancel hr.1] at this
          have h2 := abs_le.1 (abs_sr_le y hy r)
          have h3 : (0 : ℝ) ≤ (s ⟨r - 1, by omega⟩ : ℕ) := Nat.cast_nonneg _
          have h4 := le_abs_self t₀
          rw [h1]
          linarith [h2.1]
        · have : sr (X s + y) r = 0 := by simp [sr, hr]
          rw [this]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          have := abs_nonneg t₀
          linarith
      have h1 := hC i b hb (X s + y) hsr k hk
      have h2 : ∑ r ∈ Finset.range n, κ r * sr (X s + y) r ≤ S + E := by
        show _ ≤ ∑ r ∈ Finset.range n, κ r * sr (X s) r + ∑ r ∈ Finset.range n, |κ r| * (2 * n)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [sr_add, mul_add]
        have h3 : κ r * sr y r ≤ |κ r| * (2 * n) := by
          calc κ r * sr y r ≤ |κ r * sr y r| := le_abs_self _
            _ = |κ r| * |sr y r| := abs_mul _ _
            _ ≤ |κ r| * (2 * n) := mul_le_mul_of_nonneg_left (abs_sr_le y hy r) (abs_nonneg _)
        linarith
      have h3 : ‖f i (b * tor K (X s + y) * k)‖ ≤ W := by
        calc _ ≤ C * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) := h1
          _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max C 0 * Real.exp (S + E) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (le_max_right _ _)
          _ = W := by
              show _ = max C 0 * Real.exp E * Real.exp S
              rw [Real.exp_add]; ring
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h3 2)
    have hmeas : Measurable fun g => ‖f i g‖ₑ ^ 2 := ((hf i).measurable.enorm).pow_const 2
    have hexp : W ^ 2 * (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r))
        = D * ∏ j, Real.exp (a j * s j) := by
      have e1 : ∑ r ∈ Finset.range n, κ r * sr (X s) r
          = ∑ j : Fin (n - 1), κ ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e2 : ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = ∑ j : Fin (n - 1), 2 * rho K n ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr (fun r => 2 * rho K n r)]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e3 : 2 * S - ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = -t₀ * ∑ j, a j + ∑ j, a j * s j := by
        show 2 * ∑ r ∈ Finset.range n, κ r * sr (X s) r - _ = _
        rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        show _ = -t₀ * (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)))
          + (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))) * s j
        ring
      have e4 : Real.exp S ^ 2 * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)
          = Real.exp (-t₀ * ∑ j, a j) * ∏ j, Real.exp (a j * s j) := by
        rw [← Real.exp_sum, ← Real.exp_add, ← e3, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
      show (max C 0 * Real.exp E * Real.exp S) ^ 2 * _ = (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j) * _
      calc _ = (max C 0 * Real.exp E) ^ 2 * Cv * (Real.exp S ^ 2 *
              Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by ring
        _ = _ := by rw [e4]; ring
    calc ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (W ^ 2) * μ (box (X s)) :=
          setLIntegral_le_of_bound μ hmeas _ _ hnorm
      _ ≤ ENNReal.ofReal (W ^ 2) * ENNReal.ofReal
            (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by
          gcongr
          exact hCv (X s)
      _ = ENNReal.ofReal (D * ∏ j, Real.exp (a j * s j)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hexp]
      _ = _ := by
          rw [ENNReal.ofReal_mul' (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
            ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  have hsum : ∑' s : Fin (n - 1) → ℕ, ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤ :=
    tsum_pi_prod_ne_top (n - 1) (fun j k => ENNReal.ofReal (Real.exp (a j * k)))
      fun j => tsum_exp_ne_top (ha j)
  let G : (Fin (n - 1) → ℕ) → ℝ≥0∞ := fun s =>
    ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j))
  have hG : ∑' s, G s ≠ ⊤ := by
    show ∑' s : Fin (n - 1) → ℕ, ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero hG)).2 η hη).exists
  refine ⟨⋃ s ∈ F, box (X s), F.isCompact_biUnion fun s _ => isCompact_box hω (X s), fun i => ?_⟩
  have hsub : slab ω t₀ \ ⋃ s ∈ F, box (X s) ⊆ ⋃ s : {s // s ∉ F}, box (X s) := by
    rintro g ⟨hg, hgF⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 (hcover hg)
    refine Set.mem_iUnion.2 ⟨⟨s, fun hsF => hgF ?_⟩, hs⟩
    exact Set.mem_biUnion hsF hs
  calc ∫⁻ g in slab ω t₀ \ ⋃ s ∈ F, box (X s), ‖f i g‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in ⋃ s : {s // s ∉ F}, box (X s), ‖f i g‖ₑ ^ 2 ∂μ := lintegral_mono_set hsub
    _ ≤ ∑' s : {s // s ∉ F}, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' s : {s // s ∉ F}, G s := ENNReal.tsum_le_tsum fun s => hbox i s
    _ ≤ η := hF.le

theorem tail_unif : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (AdelicGLn.AdelicGL K n)] [BorelSpace (AdelicGLn.AdelicGL K n)] (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (ι : Type)
  (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), (∀ i, Continuous (f i)) → UBnd f κ → (∀ r, 0 < r → r < n → κ r < An.rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ (t₀ : ℝ) (η : ℝ≥0∞), 0 < η →
  ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  intro K _ _ n m hb μ _ ι f κ hf hB hκ ω hω hωB t₀ η hη
  have e : m = measurableSpace_adelicGL := hb.measurable_eq
  subst e
  exact tail_lib K n μ ι f κ hf hB hκ ω hω hωB t₀ η hη

end GlobalTheory.CompanionTheory.Conc.TailU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOne
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.Completion

theorem valuation_eq_exp_neg_one_of_mem_of_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F) (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.valuation F (ϖ : F) = WithZero.exp (-1 : ℤ) := by
  have hval : v.valuation F (ϖ : F) = v.intValuation ϖ := v.valuation_of_algebraMap ϖ
  rw [hval]
  have hle : v.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h1)
  have hnle : ¬ v.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((v.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have hne : v.intValuation ϖ ≠ 0 := by
    intro h
    apply hnle
    rw [h]
    exact zero_le
  rw [← WithZero.exp_log hne] at hle hnle ⊢
  rw [WithZero.exp_le_exp] at hle hnle
  congr 1
  push_cast at hle hnle
  omega

theorem ord_algebraMap_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  intro F _ _ v ϖ h1 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion F]
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    GlobalTheory.adicCompletion_valuation_map_uniformiser F v (v.adicCompletion F) (RingEquiv.refl _)
      (fun a => by
        rw [GroundTheory.Global.mem_valuationInteger_iff]
        exact Iff.rfl) π hπ
  have hx : Valued.v (algebraMap F (v.adicCompletion F) (ϖ : F)) = WithZero.exp (-1 : ℤ) := by
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ϖ : F)).trans
      (valuation_eq_exp_neg_one_of_mem_of_notMem F v ϖ h1 h2)
  have heq : valuation (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (ϖ : F)) =
      valuation (v.adicCompletion F) (π : v.adicCompletion F) :=
    le_antisymm
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hx.trans hv.symm)))
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hv.trans hx.symm)))
  have hn := (normalizedValuation_eq_iff (K := v.adicCompletion F)).2 heq
  rw [← ord_uniformizer hπ]
  simp only [ord, hn]

end GlobalTheory.CompanionTheory.Completion
end

