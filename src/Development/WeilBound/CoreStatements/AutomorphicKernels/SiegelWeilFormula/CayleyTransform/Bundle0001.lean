module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) :=
  GlobalTheory.Grow.continuous_infEmb_compInf F w τ

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) :=
  Dense.piInf_cA h τ z

theorem map_cA {p q : Type} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (X : Matrix p q (AE F E)) :
    (X.map (cA σ)).map (piInf τ) = (X.map (piInf τ)).map star :=
  Matrix.ext fun i j => piInf_cA h τ (X i j)


omit [NumberField E] in
theorem compFin_finOne (v : Pl (F := F)) (z : AE F E) : compFin F E v (finOne F • z) = compFin F E v z := by
  have e0 := St.compFin_smul (E := E) v (a := 1 - St.eF F) (sub_self (1 : Af F)) z
  rw [sub_smul, one_smul, map_sub, sub_eq_zero] at e0
  exact e0.symm

theorem ad_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : AE F E}
    (h1 : ∀ w, piInf (τ w) a = piInf (τ w) b) (h2 : finOne F • a = finOne F • b) : a = b :=
  PositivityTheory.ThKG.Tow.Levi.ad_ext h τ h1 fun v => by rw [← compFin_finOne v a, h2, compFin_finOne]

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {p q : Type} {a b : Matrix p q (AE F E)}
    (h1 : ∀ w, a.map (piInf (τ w)) = b.map (piInf (τ w))) (h2 : finOne F • a = finOne F • b) : a = b :=
  Matrix.ext fun i j => ad_ext h τ (fun w => congrFun (congrFun (h1 w) i) j) (congrFun (congrFun h2 i) j)


omit [NumberField E] in
theorem piInf_finOne {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) : piInf τ (finOne F • z) = 0 := by
  rw [St.piInf_smul]
  have : (finOne F).1 w = 0 := rfl
  rw [this, map_zero, zero_mul]

theorem exists_sec (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ x w, piInf (τ w) (s x) = x w) ∧
      (∀ x, finOne F • s x = 0) ∧ (∀ x y, s (x + y) = s x + s y) ∧ (∀ x y, s (x * y) = s x * s y) := by
  have := h.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  let ρ : (InfinitePlace F → ℝ) → AF F := fun t =>
    pairA F (fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w)) 0
  have hρ : Continuous ρ := by
    have : Continuous fun (t : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w) :=
      continuous_pi fun w => (IsometryEquiv.continuous _).comp (continuous_apply w)
    exact this.prodMk continuous_const
  have eρ : ∀ t w, InfinitePlace.Completion.extensionEmbedding w ((ρ t).1 w) = t w := fun t w => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hr w)]
    exact congrArg _ ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).apply_symm_apply (t w))
  obtain ⟨a, ha, -⟩ := PositivityTheory.ThKG.Tow.Levi.exists_inf h τ fun _ => Complex.I
  let s : (InfinitePlace F → ℂ) → AE F E := fun z => ρ (fun w => (z w).re) • 1 + ρ (fun w => (z w).im) • a
  have hs1 : ∀ x w, piInf (τ w) (s x) = x w := fun x w => by
    change piInf (τ w) (ρ (fun w => (x w).re) • 1 + ρ (fun w => (x w).im) • a) = x w
    rw [map_add (f := _), St.piInf_smul, St.piInf_smul, eρ, eρ, ha, map_one, mul_one, Complex.re_add_im]
  have hs2 : ∀ x v, compFin F E v (s x) = 0 := fun x v => by
    change compFin F E v (ρ (fun w => (x w).re) • 1 + ρ (fun w => (x w).im) • a) = 0
    rw [map_add (f := _), St.compFin_smul v rfl, St.compFin_smul v rfl, add_zero]
  have hc : Continuous s := by
    have h1 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).re :=
      hρ.comp (continuous_pi fun w => Complex.continuous_re.comp (continuous_apply w))
    have h2 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).im :=
      hρ.comp (continuous_pi fun w => Complex.continuous_im.comp (continuous_apply w))
    have h3 : ∀ b : AE F E, Continuous fun x : AF F => x • b := fun b =>
      Continuous.fun_smul (f := fun x : AF F => x) (g := fun _ => b) continuous_id' continuous_const
    exact Continuous.fun_add (f := fun z : InfinitePlace F → ℂ => ρ (fun w => (z w).re) • (1 : AE F E))
      (g := fun z => ρ (fun w => (z w).im) • a) ((h3 1).comp' h1) ((h3 a).comp' h2)
  clear_value s
  have ext' : ∀ b c : AE F E, (∀ w, piInf (τ w) b = piInf (τ w) c) → (∀ v, compFin F E v b = compFin F E v c) → b = c :=
    fun b c h1 h2 => PositivityTheory.ThKG.Tow.Levi.ad_ext h τ h1 h2
  refine ⟨s, hc, hs1, fun x => ?_, fun x y => ?_, fun x y => ?_⟩
  · refine ext' _ _ (fun w => ?_) fun v => ?_
    · rw [piInf_finOne, map_zero]
    · rw [compFin_finOne, hs2, map_zero]
  · refine ext' _ _ (fun w => ?_) fun v => ?_
    · rw [map_add (f := _), hs1, hs1, hs1, Pi.add_apply]
    · rw [map_add (f := _), hs2, hs2, hs2, add_zero]
  · refine ext' _ _ (fun w => ?_) fun v => ?_
    · rw [map_mul, hs1, hs1, hs1, Pi.mul_apply]
    · rw [map_mul, hs2, hs2, hs2, zero_mul]

theorem at_of_finOne {a : AF F} (hf : finOne F * a = 0) : At (evI F) a := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  have e : u = u * finOne F :=
    Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])
  rw [smul_eq_mul, e, mul_assoc, hf, mul_zero]

theorem psi_at {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hF : IsTotallyReal F) (w : InfinitePlace F) (a : AF F)
    (hf : finOne F * a = 0) (hw : ∀ u, u ≠ w → InfinitePlace.Completion.extensionEmbedding u (a.1 u) = 0) :
    ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * ((InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re : ℂ)) := by
  rw [hψ.2.2 a (at_of_finOne hf), Dense.trace_evI hF, Finset.sum_eq_single w (fun u _ hu => by rw [hw u hu, Complex.zero_re])
    (fun hw' => absurd (Finset.mem_univ w) hw')]

theorem psi_trace_at {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (w : InfinitePlace F) (z : AE F E) (hf : finOne F • z = 0) (hw : ∀ u, u ≠ w → piInf (τ u) z = 0) :
    ψ (Algebra.trace (AF F) (AE F E) z) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (piInf (τ w) z).re : ℝ) : ℂ)) := by
  have e : ∀ u, InfinitePlace.Completion.extensionEmbedding u ((Algebra.trace (AF F) (AE F E) z).1 u) =
      piInf (τ u) z + star (piInf (τ u) z) := fun u => by rw [Dense.ext_trace h (τ u), Dense.piInf_cA h]
  have hf' : finOne F * Algebra.trace (AF F) (AE F E) z = 0 := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, hf, map_zero]
  rw [psi_at hψ h.1 w _ hf' fun u hu => by rw [e u, hw u hu, star_zero, add_zero], e w]
  congr 3
  rw [Complex.add_re, Complex.star_def, Complex.conj_re, two_mul]

variable (d : SD σ)

theorem _root_.PositivityTheory.SiegelWeilFormula.SD.cm (d : SD σ) : IsCMExt F E σ := d.ok.good.cm

theorem _root_.PositivityTheory.SiegelWeilFormula.SD.std (d : SD σ) : IsStd d.B.ψ := d.ok.good.std

theorem continuous_cw (w : InfinitePlace F) {p q : Type} : Continuous (fun X : Matrix p q (AE F E) => d.cw w X) :=
  continuous_id.matrix_map (continuous_piInf (d.B.emb w))

theorem cw_ext {p q : Type} {X Z : Matrix p q (AE F E)} (h1 : ∀ w, d.cw w X = d.cw w Z) (h2 : finOne F • X = finOne F • Z) :
    X = Z :=
  mat_ext d.cm d.B.emb h1 h2

theorem cw_cA (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) : d.cw w (X.map (cA σ)) = (d.cw w X).map star :=
  map_cA d.cm _ X

end PositivityTheory.SiegelWeilFormula.Place

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DZTranspose
section
noncomputable section

open scoped Matrix
open PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd

variable {n : ℕ}

def Qc (n : ℕ) (ε : ℤˣ) : M2 n := Matrix.fromBlocks 0 1 (((ε : ℤ) : ℂ) • 1) 0

theorem mapStar_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) : (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem mapStar_one {ι : Type} [DecidableEq ι] : (1 : Matrix ι ι ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem dZ_mul (a b : ℂ) : dZ n a * dZ n b = dZ n (a * b) := by
  simp [dZ, Matrix.fromBlocks_multiply, smul_smul, mul_comm]

theorem dZ_one : dZ n 1 = 1 := by
  simp [dZ, Matrix.fromBlocks_one]

theorem dZ_transpose (a : ℂ) : (dZ n a)ᵀ = dZ n a := by
  simp [dZ, Matrix.fromBlocks_transpose]

theorem dZ_map_star (a : ℂ) : (dZ n a).map star = dZ n (star a) := by
  unfold dZ
  rw [Matrix.fromBlocks_map]
  simp [mapStar_one]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem dZ_inv_mul {ζ : ℂ} (h : ζ ≠ 0) : dZ n ζ⁻¹ * dZ n ζ = 1 := by
  rw [dZ_mul, inv_mul_cancel₀ h, dZ_one]

theorem dZ_mul_inv {ζ : ℂ} (h : ζ ≠ 0) : dZ n ζ * dZ n ζ⁻¹ = 1 := by
  rw [dZ_mul, mul_inv_cancel₀ h, dZ_one]

theorem zeta_ne {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) : ζ ≠ 0 := by
  rcases hζ with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact one_ne_zero
  · exact Complex.I_ne_zero

theorem mid {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    dZ n ζ⁻¹ * Qc n ε * dZ n (star ζ⁻¹) = ζ • JJ n := by
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, smul_smul, Complex.inv_I]

theorem outer {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    dZ n ζ * (ζ • JJ n) * dZ n (star ζ) = Qc n ε := by
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, smul_smul]

theorem key {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (g : M2 n) :
    (dZ n ζ⁻¹ * g * dZ n ζ)ᵀ * Qc n ε * (dZ n ζ⁻¹ * g * dZ n ζ).map star =
      dZ n ζ * (ζ • (gᵀ * JJ n * g.map star)) * dZ n (star ζ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, dZ_transpose, dZ_transpose, mapStar_mul, mapStar_mul,
    dZ_map_star, dZ_map_star]
  have e : ζ • (gᵀ * JJ n * g.map star) = gᵀ * (ζ • JJ n) * g.map star := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, ← mid (n := n) hζ]
  simp only [Matrix.mul_assoc]

theorem conj_JJ (g : M2 n) : gᵀ * JJ n * g.map star = JJ n ↔ gᴴ * JJ n * g = JJ n := by
  have key2 : ∀ A : M2 n, (A.map star).map star = A := fun A => by
    ext i j
    simp
  have hJ : (JJ n).map star = JJ n := by
    unfold JJ
    rw [Matrix.fromBlocks_map]
    simp [mapStar_one]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have e : (gᵀ * JJ n * g.map star).map star = gᴴ * JJ n * g := by
    rw [mapStar_mul, mapStar_mul, hJ, key2]
    rfl
  constructor
  · intro h
    rw [← e, h, hJ]
  · intro h
    rw [← e] at h
    rw [← key2 (gᵀ * JJ n * g.map star), h, hJ]

theorem unitary_iff {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (g : M2 n) :
    (dZ n ζ⁻¹ * g * dZ n ζ)ᵀ * Qc n ε * (dZ n ζ⁻¹ * g * dZ n ζ).map star = Qc n ε ↔ InG g := by
  have hz := zeta_ne hζ
  have hs : star ζ ≠ 0 := star_ne_zero.mpr hz
  have canc : ∀ A : M2 n, dZ n ζ⁻¹ * (dZ n ζ * A * dZ n (star ζ)) * dZ n (star ζ)⁻¹ = A := by
    intro A
    simp only [Matrix.mul_assoc, dZ_mul_inv hs, Matrix.mul_one]
    rw [← Matrix.mul_assoc, dZ_inv_mul hz, Matrix.one_mul]
  have hI : InG g ↔ gᵀ * JJ n * g.map star = JJ n := (conj_JJ g).symm
  rw [key hζ, ← outer (n := n) hζ, hI]
  constructor
  · intro h
    have h2 := canc (ζ • (gᵀ * JJ n * g.map star))
    rw [h, canc] at h2
    exact smul_right_injective _ hz h2.symm
  · intro h
    rw [h]

theorem inG_conj {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (Z : M2 n)
    (hZ : Zᵀ * Qc n ε * Z.map star = Qc n ε) : InG (dZ n ζ * Z * dZ n ζ⁻¹) := by
  have hz := zeta_ne hζ
  have e : dZ n ζ⁻¹ * (dZ n ζ * Z * dZ n ζ⁻¹) * dZ n ζ = Z := by
    simp only [Matrix.mul_assoc, dZ_inv_mul hz, Matrix.mul_one]
    rw [← Matrix.mul_assoc, dZ_inv_mul hz, Matrix.one_mul]
  rw [← unitary_iff hζ, e]
  exact hZ

end PositivityTheory.SiegelWeilFormula.Krd

end
end

