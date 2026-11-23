module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SimultaneousNormalFormMajorant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Diag


open scoped MatrixOrder in
theorem exists_eq_transpose_mul_self {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℝ} (hT : T.PosSemidef) : ∃ B : Matrix ι ι ℝ, T = Bᵀ * B := by
  have hH := hT.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hspec : T = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := hH.spectral_theorem
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec
  have hd : diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      diagonal (fun i => Real.sqrt (hH.eigenvalues i)) *
        diagonal (fun i => Real.sqrt (hH.eigenvalues i)) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact (Real.mul_self_sqrt (hT.eigenvalues_nonneg i)).symm
  refine ⟨diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ, ?_⟩
  rw [transpose_mul, transpose_transpose, diagonal_transpose]
  conv_lhs => rw [hspec, hd]
  simp only [Matrix.mul_assoc]

theorem simultaneous_normal_form_majorant :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 →
      P.PosDef → P * S⁻¹ * P = S →
      ∃ (g : Matrix ι ι ℝ) (e : ι → ℝ), g.det ≠ 0 ∧ (∀ i, e i = 1 ∨ e i = -1) ∧
        gᵀ * P * g = 1 ∧ gᵀ * S * g = Matrix.diagonal e := by
  intro ι _ _ S P hS hSdet hP hPS
  obtain ⟨B, hB⟩ := exists_eq_transpose_mul_self hP.posSemidef
  have hPdet : P.det ≠ 0 := hP.det_pos.ne'
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hPdet
    rw [hB, det_mul, det_transpose, h, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  set C := B⁻¹ with hCdef
  have hBC : B * C = 1 := mul_nonsing_inv B hBu
  have hCB : C * B = 1 := nonsing_inv_mul B hBu
  have hCPC : Cᵀ * P * C = 1 := by
    rw [hB]
    calc Cᵀ * (Bᵀ * B) * C = (B * C)ᵀ * (B * C) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, transpose_one, Matrix.one_mul]
  have hPCC : P * (C * Cᵀ) = 1 := by
    rw [hB]
    calc Bᵀ * B * (C * Cᵀ) = Bᵀ * ((B * C) * Cᵀ) := by simp only [Matrix.mul_assoc]
      _ = (C * B)ᵀ := by rw [hBC, Matrix.one_mul, transpose_mul]
      _ = 1 := by rw [hCB, transpose_one]
  have hCC : C * Cᵀ = P⁻¹ := (inv_eq_right_inv hPCC).symm
  have hSPS : S * P⁻¹ * S = P := by
    calc S * P⁻¹ * S = P * S⁻¹ * P * P⁻¹ * S := by rw [hPS]
      _ = P * S⁻¹ * (P * P⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = P := by
          rw [mul_nonsing_inv P hPu, Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul S hSu,
            Matrix.mul_one]
  set A := Cᵀ * S * C with hAdef
  have hAT : Aᵀ = A := by
    simp only [hAdef, transpose_mul, transpose_transpose, hS.eq, Matrix.mul_assoc]
  have hA : A.IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hAT
  have hA2 : A * A = 1 := by
    calc A * A = Cᵀ * (S * (C * Cᵀ) * S) * C := by simp only [hAdef, Matrix.mul_assoc]
      _ = 1 := by rw [hCC, hSPS, hCPC]
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  set e : ι → ℝ := RCLike.ofReal ∘ hA.eigenvalues with hedef
  have hspec : A = U * diagonal e * star U := hA.spectral_theorem
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec hU1 hU2
  have hD : Uᵀ * A * U = diagonal e := by
    rw [hspec]
    calc Uᵀ * (U * diagonal e * Uᵀ) * U = (Uᵀ * U) * diagonal e * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal e := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hDD : diagonal e * diagonal e = 1 := by
    rw [← hD]
    calc Uᵀ * A * U * (Uᵀ * A * U) = Uᵀ * (A * (U * Uᵀ) * A) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hA2, Matrix.mul_one, hU1]
  have he : ∀ i, e i = 1 ∨ e i = -1 := by
    intro i
    have h := congrFun (congrFun hDD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h
    exact mul_self_eq_one_iff.mp h
  refine ⟨C * U, e, ?_, he, ?_, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have h' := congrArg det hCB
      rw [det_mul, h, zero_mul, det_one] at h'
      exact zero_ne_one h'
    · intro h
      have h' := congrArg det hU1
      rw [det_mul, h, mul_zero, det_one] at h'
      exact zero_ne_one h'
  · calc (C * U)ᵀ * P * (C * U) = Uᵀ * (Cᵀ * P * C) * U := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCPC, Matrix.mul_one, hU1]
  · calc (C * U)ᵀ * S * (C * U) = Uᵀ * A * U := by
          rw [transpose_mul]
          simp only [hAdef, Matrix.mul_assoc]
      _ = diagonal e := hD

end GlobalTheory.CompanionTheory.SW.Diag
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def toA (x : ι → F) : ι → A F := fun j => algebraMap F (A F) (x j)

theorem oh_add {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F :=
  fun v => add_mem (hx v) (hy v)

theorem oh_zero : (0 : A F) ∈ Oh F := fun _ => zero_mem _

theorem oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v => neg_mem (hx v)


variable (ι F) in
def latN (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨z, hz, e'⟩ := hb i
    exact ⟨y + z, oh_add hy hz, by simp [e, e', mul_add]⟩
  zero_mem' := fun i => ⟨0, oh_zero, by simp⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, oh_neg hy, by simp [e]⟩

def indC (N : ℕ) (a : ι → F) : (ι → A F) → ℂ :=
  Set.indicator {x | x - toA a ∈ latN F ι N} fun _ => 1

def emb (ρ : InfinitePlace F → (F →+* ℝ)) (x : ι → F) : ι × InfinitePlace F → ℝ :=
  fun p => ρ p.2 (x p.1)

def cur (x : ι × InfinitePlace F → ℝ) : InfinitePlace F → ι → ℝ := fun w i => x (i, w)

def DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  blockDiagonal fun w => B.map (ρ w)

def ZM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℂ :=
  blockDiagonal fun w => fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

def EM (ρ : InfinitePlace F → (F →+* ℝ)) (b : InfinitePlace F → 𝓞 F) :
    Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
  fun w v => ρ w (b v : F)

def gM [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  (N : ℝ) • ((1 : Matrix ι ι ℝ) ⊗ₖ EM ρ b)

theorem sum_rho_eq_trace {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (c : F) :
    ∑ w, ρ w c = ((Algebra.trace ℚ F c : ℚ) : ℝ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := c)
  have hb : Function.Bijective
      (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) := by
    constructor
    · intro w v h
      have : w.embedding = v.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding v, this]
    · intro σ
      refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
      have hr : (InfinitePlace.mk σ.toRingHom).IsReal := hT.isReal _
      have he := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp hr)
      ext x
      show ((InfinitePlace.mk σ.toRingHom).embedding) x = σ x
      rw [he]
      rfl
  have h2 : ∑ σ : F →ₐ[ℚ] ℂ, σ c = ∑ w : InfinitePlace F, w.embedding c := by
    rw [← (Equiv.ofBijective _ hb).sum_comp]
    rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [hρ]
  rw [← h2, ← h1]
  simp

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularity
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThetaUD

variable {F : Type} [Field F] [NumberField F]

theorem form_mulVec {R ι : Type} [CommRing R] [Fintype ι] (G Q : Matrix ι ι R) (h : Gᵀ * Q * G = Q)
    (v : ι → R) : (G *ᵥ v) ⬝ᵥ (Q *ᵥ (G *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by
  conv_rhs => rw [← h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

theorem form_map {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : Matrix ι ι R)
    (x : ι → R) : (fun j => f (x j)) ⬝ᵥ (Q.map f *ᵥ fun j => f (x j)) = f (x ⬝ᵥ (Q *ᵥ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec f Q x i).symm

theorem trace_eq_sum (hT : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (y : F) :
    ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ w, ((ρ w y : ℝ) : ℂ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  have h2 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by simp
  rw [h2, h1]
  symm
  refine Fintype.sum_bijective (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) ?_ _ _ ?_
  · constructor
    · intro w w' h
      have : w.embedding = w'.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', this]
    · intro σ
      have hr : (InfinitePlace.mk (σ : F →+* ℂ)).IsReal := hT.isReal _
      have hc : ComplexEmbedding.IsReal (σ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 hr
      refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
      ext x
      have := InfinitePlace.embedding_mk_eq_of_isReal hc
      simp [this]
  · intro w
    simp [hρ]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_add (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => τ w + (c w : ℝ)) y = gauss B ρ P τ y *
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ∑ w, ((c w : ℂ) * ((y w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
  unfold gauss
  rw [← Complex.exp_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  push_cast
  ring

theorem gauss_sq (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => ((c w : ℝ) : ℂ) ^ 2 * τ w) y = gauss B ρ P τ (fun w => c w • y w) := by
  unfold gauss
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : (((c w : ℝ) : ℂ) ^ 2 * τ w).re = c w ^ 2 * (τ w).re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have him : (((c w : ℝ) : ℂ) ^ 2 * τ w).im = c w ^ 2 * (τ w).im := by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  rw [hre, him]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring

theorem term_U (ψ : AddChar (A F) ℂ) (hψ : IsStdChar F ψ) (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (hQ : QSetup M B ρ P)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (hO : IsOrth B ρ gf gi)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (b : F) (x : ι → F) :
    thTerm B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) x =
      thTerm B ρ P gf gi φ τ x := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  obtain ⟨hOf, hOi⟩ := hO
  set t : F := x ⬝ᵥ (B *ᵥ x) with ht
  have hfin : qf (hf F) (Bf B) (gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      algebraMap F (A F) (1 / 2 * t) := by
    unfold qf
    rw [form_mulVec gf (Bf B) hOf]
    have := form_map (algebraMap F (A F)) B x
    unfold Bf hf
    rw [this, map_mul]
  have hinf : ∀ w, (gi w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (B.map (ρ w) *ᵥ (gi w *ᵥ fun j => ρ w (x j))) =
      ρ w t := by
    intro w
    rw [form_mulVec (gi w) _ (hOi w), form_map]
  have hphase : ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) = 1 := by
    rw [← map_mul, hψ.2, trace_eq_sum hT ρ hρ, ← Complex.exp_add]
    have : ∑ w, ((ρ w (b * (1 / 2 * t)) : ℝ) : ℂ) = (1 / 2) * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [map_mul, map_div₀, map_one, map_ofNat]
      push_cast
      ring
    rw [this]
    have h0 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) +
        (Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  unfold thTerm opU
  rw [gauss_add B ρ P τ (fun w => ρ w b), hfin]
  simp only [hinf]
  calc _ = (ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)))) *
        (φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) *
          gauss B ρ P τ fun w => gi w *ᵥ fun j => ρ w (x j)) := by ring
    _ = _ := by rw [hphase, one_mul]

theorem term_D (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (a : F) (x : ι → F) :
    thTerm B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) x =
      thTerm B ρ P gf gi φ τ (a • x) := by
  unfold thTerm opD
  rw [gauss_sq B ρ P τ (fun w => ρ w a)]
  have h1 : (algebraMap F (A F) a • gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      gf *ᵥ fun j => algebraMap F (A F) ((a • x) j) := by
    rw [← Matrix.mulVec_smul]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  have h2 : (fun w => ρ w a • gi w *ᵥ fun j => ρ w (x j)) =
      fun w => gi w *ᵥ fun j => ρ w ((a • x) j) := by
    funext w
    rw [← Matrix.mulVec_smul]
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  intro F _ _ ψ hψ ι _ _ M B ρ P hQ gf gi hO φ τ
  refine ⟨fun b => ?_, fun a ha => ?_, fun c => ?_⟩
  · unfold theta
    exact tsum_congr fun x => term_U ψ hψ M B ρ P hQ gf gi hO φ τ b x
  · unfold theta
    simp only [term_D]
    exact (MulAction.toPerm (Units.mk0 a ha) : Equiv.Perm (ι → F)).tsum_eq (thTerm B ρ P gf gi φ τ)
  · unfold theta
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [thTerm, mul_assoc]

end GlobalTheory.CompanionTheory.SW.ThetaUD
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitBalancingImaginaryParts
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.UnitBalance


open NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem exists_bound_log_centered (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (s : ℝ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E)) - s| ≤ R := by
  classical
  let B := (NumberField.Units.basisUnitLattice E).ofZLatticeBasis ℝ
    (NumberField.Units.unitLattice E)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  refine ⟨Fintype.card (InfinitePlace E) * |C|, fun t => ?_⟩
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  let s : ℝ := (∑ w : InfinitePlace E, (w.mult : ℝ) * t w) / Module.finrank ℚ E
  let l : logSpace E := fun w => (w.1.mult : ℝ) * (t w.1 - s)
  obtain ⟨⟨e, he⟩, h2, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B l
  rw [Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice E)] at he
  obtain ⟨u, -, rfl⟩ := he
  let a : InfinitePlace E → ℝ := fun w => (w.mult : ℝ) * (t w - s + Real.log (w (u.toMul : E)))
  have hsum : ∑ w, a w = 0 := by
    have h1 := sum_mult_mul_log (K := E) u.toMul
    have h3 : ∑ w : InfinitePlace E, (w.mult : ℝ) = Module.finrank ℚ E := by
      exact_mod_cast InfinitePlace.sum_mult_eq (K := E)
    simp only [a, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, h3, s]
    field_simp
    ring
  have ha : ∀ w, w ≠ w₀ → |a w| ≤ |C| := fun w hw => by
    have h4 := (norm_le_pi_norm _ (⟨w, hw⟩ : {w : InfinitePlace E // w ≠ w₀})).trans (hC _ h2)
    refine le_trans (le_of_eq ?_) (h4.trans (le_abs_self C))
    rw [Real.norm_eq_abs]
    congr 1
    change _ = (w.mult : ℝ) * Real.log (w (u.toMul : E)) + (w.mult : ℝ) * (t w - s)
    simp only [a]
    ring
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
  have ha' : ∀ w, |a w| ≤ Fintype.card (InfinitePlace E) * |C| := fun w => by
    by_cases hw : w = w₀
    · subst hw
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀), add_eq_zero_iff_eq_neg] at hsum
      rw [hsum, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun w hw => ha w (Finset.ne_of_mem_erase hw)).trans ?_
      rw [nsmul_eq_mul]
      gcongr
      exact Finset.card_le_univ _
    · exact (ha w hw).trans (le_mul_of_one_le_left (abs_nonneg C) hcard)
  refine ⟨u.toMul, s, fun w => ?_⟩
  have h5 : |t w - s + Real.log (w (u.toMul : E))| ≤ |a w| := by
    simp only [a]
    rw [abs_mul]
    refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [Nat.abs_cast]
    exact_mod_cast w.mult_pos
  have h6 := h5.trans (ha' w)
  have h7 : t w + Real.log (w (u.toMul : E)) - s = t w - s + Real.log (w (u.toMul : E)) := by ring
  rw [h7]
  exact h6

theorem balance_by_units : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  intro F _ _ _ ρ hρ
  obtain ⟨R, hR⟩ := exists_bound_log_centered F
  refine ⟨Real.exp (-(4 * R)), Real.exp_pos _, fun y hy => ?_⟩
  obtain ⟨u, s, hu⟩ := hR (fun w => Real.log (y w) / 2)
  refine ⟨u, fun v w => ?_⟩
  have hne : ((u : 𝓞 F) : F) ≠ 0 := NumberField.Units.coe_ne_zero u
  have hexp : ∀ w : InfinitePlace F, ρ w ((u : 𝓞 F) : F) ^ 2 * y w =
      Real.exp (2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F)))) := by
    intro w
    have habs : w ((u : 𝓞 F) : F) = |ρ w ((u : 𝓞 F) : F)| := by
      rw [← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < w ((u : 𝓞 F) : F) := w.pos_iff.2 hne
    have e1 : 2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F))) =
        Real.log (w ((u : 𝓞 F) : F)) + Real.log (w ((u : 𝓞 F) : F)) + Real.log (y w) := by ring
    rw [e1, Real.exp_add, Real.exp_add, Real.exp_log hpos, Real.exp_log (hy w), habs, ← sq, sq_abs]
  rw [hexp v, hexp w, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := abs_le.1 (hu v)
  have h2 := abs_le.1 (hu w)
  linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.SW.UnitBalance
end

