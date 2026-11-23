module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.Bundle0001
public import GroundTheory.PAdicHodge.NormalizedTrace

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FrameBlockPairingSign
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Matrix

section Place

variable {m n : ℕ}

def T1 (A : Matrix (Fin m) (Fin m) ℂ) (C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : Matrix (Fin m) (Fin n) ℂ)
    (V : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  trace ((x * (bw.toCols₂)ᵀ)ᵀ * A * (V * (bw.toCols₁)ᵀ).map star * Cᵀ)

def T2 (fi : Matrix (Fin m) (Fin m) ℂ) (x V : Matrix (Fin m) (Fin n) ℂ) : ℂ := trace ((fi * x)ᴴ * (fi * V))

def Sw (A fi : Matrix (Fin m) (Fin m) ℂ) (C bw biw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (x : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ) : ℂ :=
  (4 * Real.pi * Complex.I) * ((T1 A C bw x (U * biwᵀ).toCols₁).re : ℂ) -
    (4 * Real.pi) * ((T2 fi x (U * biwᵀ).toCols₂).re : ℂ)

theorem frame_block_pairing_sign {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε : ℤˣ} (hJ : bwᵀ * C * bw.map star = jE n ε) :
    (bw.toCols₂)ᵀ * C * (bw.toCols₁).map star = ((ε : ℤ) : ℂ) • 1 := by
  ext i j
  have h := congrFun (congrFun hJ (Sum.inr i)) (Sum.inl j)
  simp only [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.fromBlocks_apply₂₁] at h
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.toCols₁_apply,
    Matrix.toCols₂_apply]

theorem mapStar_mul {a b c : Type} [Fintype b] (M : Matrix a b ℂ) (N : Matrix b c ℂ) :
    (M * N).map star = M.map star * N.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

theorem trace_form_sign_eq {A : Matrix (Fin m) (Fin m) ℂ} {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε : ℤˣ}
    (hJ : bwᵀ * C * bw.map star = jE n ε) (x V : Matrix (Fin m) (Fin n) ℂ) :
    T1 A C bw x V = ((ε : ℤ) : ℂ) * trace (xᵀ * A * V.map star) := by
  have h1 := PositivityTheory.SiegelWeilFormula.KK.frame_block_pairing_sign hJ
  have h2 : ((bw.toCols₁).map star)ᵀ * Cᵀ * bw.toCols₂ = ((ε : ℤ) : ℂ) • 1 := by
    have h := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul,
      Matrix.transpose_one, ← Matrix.mul_assoc] at h
    exact h
  unfold PositivityTheory.SiegelWeilFormula.KK.T1
  calc trace ((x * (bw.toCols₂)ᵀ)ᵀ * A * (V * (bw.toCols₁)ᵀ).map star * Cᵀ)
      = trace (bw.toCols₂ * (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ))) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, PositivityTheory.SiegelWeilFormula.KK.mapStar_mul,
          Matrix.transpose_map, Matrix.mul_assoc]
    _ = trace (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ) * bw.toCols₂) :=
        Matrix.trace_mul_comm _ _
    _ = trace (xᵀ * A * V.map star * (((bw.toCols₁).map star)ᵀ * Cᵀ * bw.toCols₂)) := by
        simp only [Matrix.mul_assoc]
    _ = trace (xᵀ * A * V.map star * (((ε : ℤ) : ℂ) • 1)) := by rw [h2]
    _ = ((ε : ℤ) : ℂ) * trace (xᵀ * A * V.map star) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

theorem trace_transpose_star {a b : Type} [Fintype a] [Fintype b] (M N : Matrix a b ℂ) :
    trace (Mᵀ * N.map star) = star (trace (Mᴴ * N)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, star_sum, star_mul', star_star]

theorem A_eq {A fr fi : Matrix (Fin m) (Fin m) ℂ} {sg : ℤˣ} {ζ : ℂ} (hfi' : fr * fi = 1) (hz : star ζ * ζ = 1)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) :
    A = (((sg : ℤ) : ℂ) * star ζ) • (fiᵀ * fi.map star) := by
  have h1 : frᵀ * A * fr.map star = (((sg : ℤ) : ℂ) * star ζ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have h := congrArg (fun M => star ζ • M) hfr
    simp only [smul_smul, hz, one_smul] at h
    rw [h, mul_comm]
  have hfi : fiᵀ * frᵀ = 1 := by rw [← Matrix.transpose_mul, hfi', Matrix.transpose_one]
  have hfi2 : fr.map star * fi.map star = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.KK.mapStar_mul, hfi']
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  calc A = fiᵀ * frᵀ * A * (fr.map star * fi.map star) := by
        rw [hfi, hfi2, Matrix.one_mul, Matrix.mul_one]
    _ = fiᵀ * (frᵀ * A * fr.map star) * fi.map star := by simp only [Matrix.mul_assoc]
    _ = fiᵀ * ((((sg : ℤ) : ℂ) * star ζ) • (1 : Matrix (Fin m) (Fin m) ℂ)) * fi.map star := by rw [h1]
    _ = (((sg : ℤ) : ℂ) * star ζ) • (fiᵀ * fi.map star) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem trace_form_dual_eq {A fr fi : Matrix (Fin m) (Fin m) ℂ} {C bw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε sg : ℤˣ} {ζ : ℂ} (hfi' : fr * fi = 1) (hz : star ζ * ζ = 1)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) (hJ : bwᵀ * C * bw.map star = jE n ε)
    (x V : Matrix (Fin m) (Fin n) ℂ) :
    T1 A C bw x V = ((ε : ℤ) : ℂ) * ((((sg : ℤ) : ℂ) * star ζ) * star (T2 fi x V)) := by
  rw [PositivityTheory.SiegelWeilFormula.KK.trace_form_sign_eq hJ,
    PositivityTheory.SiegelWeilFormula.KK.A_eq hfi' hz hfr]
  congr 1
  unfold PositivityTheory.SiegelWeilFormula.KK.T2
  rw [← PositivityTheory.SiegelWeilFormula.KK.trace_transpose_star, Matrix.transpose_mul, PositivityTheory.SiegelWeilFormula.KK.mapStar_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem Sw_rel {A fr fi : Matrix (Fin m) (Fin m) ℂ} {C bw biw : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {ε sg : ℤˣ}
    {ζ : ℂ} (e2 : biw * bw = 1) (hfi' : fr * fi = 1) (hJ : bwᵀ * C * bw.map star = jE n ε)
    (hfr : ζ • (frᵀ * A * fr.map star) = ((sg : ℤ) : ℂ) • 1) (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I)
    (x : Matrix (Fin m) (Fin n) ℂ) (U U' : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ)
    (hU : U' = (((((1 : ℤˣ) : ℤ) : ℂ) * Complex.I) • ((-(Complex.I * ((((ε : ℤ) : ℂ) * ((sg : ℤ) : ℂ)) * ζ))) •
      (1 : Matrix (Fin m) (Fin m) ℂ) * U * (bw * (jE n ε)ᵀ * biw)ᵀ))) :
    Sw A fi C bw biw x U' = Complex.I * Sw A fi C bw biw x U := by
  have hz : star ζ * ζ = 1 := by
    rcases hζ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have hW : (bw * (PositivityTheory.SiegelWeilFormula.KK.jE n ε)ᵀ * biw)ᵀ * biwᵀ = biwᵀ * PositivityTheory.SiegelWeilFormula.KK.jE n ε := by
    rw [← Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have hUb : U' * biwᵀ = (((((1 : ℤˣ) : ℤ) : ℂ) * Complex.I) * (-(Complex.I * ((((ε : ℤ) : ℂ) * ((sg : ℤ) : ℂ)) * ζ)))) •
      (U * biwᵀ * PositivityTheory.SiegelWeilFormula.KK.jE n ε) := by
    rw [hU, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc U _ biwᵀ, hW, ← Matrix.mul_assoc]
  have hYS1 : ∀ Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ,
      (Y * PositivityTheory.SiegelWeilFormula.KK.jE n ε).toCols₁ = ((ε : ℤ) : ℂ) • Y.toCols₂ := by
    intro Y
    ext i j
    simp [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    try ring
  have hYS2 : ∀ Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ,
      (Y * PositivityTheory.SiegelWeilFormula.KK.jE n ε).toCols₂ = Y.toCols₁ := by
    intro Y
    ext i j
    simp [PositivityTheory.SiegelWeilFormula.KK.jE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    try ring
  have hts1 : ∀ (c : ℂ) (M : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ), (c • M).toCols₁ = c • M.toCols₁ :=
    fun _ _ => Matrix.ext fun _ _ => rfl
  have hts2 : ∀ (c : ℂ) (M : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ), (c • M).toCols₂ = c • M.toCols₂ :=
    fun _ _ => Matrix.ext fun _ _ => rfl
  have hT : ∀ V, PositivityTheory.SiegelWeilFormula.KK.T1 A C bw x V =
      ((ε : ℤ) : ℂ) * ((((sg : ℤ) : ℂ) * star ζ) * star (PositivityTheory.SiegelWeilFormula.KK.T2 fi x V)) :=
    PositivityTheory.SiegelWeilFormula.KK.trace_form_dual_eq hfi' hz hfr hJ x
  have hN : ∀ (c : ℂ) (V : Matrix (Fin m) (Fin n) ℂ),
      PositivityTheory.SiegelWeilFormula.KK.T2 fi x (c • V) = c * PositivityTheory.SiegelWeilFormula.KK.T2 fi x V := by
    intro c V
    unfold PositivityTheory.SiegelWeilFormula.KK.T2
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  unfold PositivityTheory.SiegelWeilFormula.KK.Sw
  rw [hUb, hts1, hts2, hYS1, hYS2, smul_smul, hT, hT, hN, hN]
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases Int.units_eq_one_or sg with rfl | rfl <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end Place

end PositivityTheory.SiegelWeilFormula.KK

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.Splitting
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem splitting (d : SD σ) : IsSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om :=
  d.ok.dbl.weil.2.1.toIsSplitting

theorem imp (d : SD σ) (k : d.G) :
    Box.Imp d.B.ψ (d.om k) fun w => d.dd.e (actB (cA σ) k (d.dd.e.symm w)) :=
  ⟨(splitting d).pres k, (splitting d).adm k, fun w w' => by simp only [actB, map_add (f := _), Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := (splitting d).impl k (d.dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩

theorem om_D (k : d.G) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) : d.om k (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e (actB (cA σ) k u)) (d.om k Φ) := by
  have := (imp d k).inter d.ok.good.std (Box.at_e d.dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this

theorem D_kfS {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) {Φ : d.Fn} (h : Φ ∈ kfS d) :
    Box.D (d.dd.e u) Φ ∈ kfS d := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := Box.exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = Box.D (d.dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact Box.DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, Box.at_actB k hv, _, h2 k hk x hx, om_D k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i

theorem vac_kfS (θ : InfinitePlace F → Matrix (Fin d.m) (Fin d.m) ℂ)
    (θ' : InfinitePlace F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ)
    (hc : ∀ k ∈ d.K, ∀ w, Commute ((mat2 k).map (piInf (d.B.emb w))) (θ' w)) (ε : InfinitePlace F → ℤˣ) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : ∀ u u', At (evI F) u → At (evI F) u' → Box.Rel d.B.emb ε θ θ' u u' →
      Box.D (d.dd.e u') Φ = Complex.I • Box.D (d.dd.e u) Φ) : Φ ∈ kfS d := by
  have hB := d.ok.good
  have hs := splitting d
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := finLevel F E σ d.B d.m d.n d.A d.Y hB d.κ d.dd d.K (isCompact_K d) Φ hΦ
  have radd : ∀ u (x y : d.Fn), d.dd.rho d.B.ψ u (x + y) = d.dd.rho d.B.ψ u x + d.dd.rho d.B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : d.Fn), d.dd.rho d.B.ψ u (c • x) = c • d.dd.rho d.B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ d.Fn :=
    { carrier := {Ψ | Ψ ∈ d.sch ∧ (∀ u ∈ Λ, d.dd.rho d.B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Box.Rel d.B.emb ε θ θ' u u' → Box.D (d.dd.e u') Ψ = Complex.I • Box.D (d.dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by
        simp only [Box.D, Box.DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [Box.D] at e1 e2 ⊢
        rw [Box.DP_add h.1 h'.1, Box.DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [Box.D] at e1 ⊢
        rw [Box.DP_smul h.1, Box.DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : d.κ → AF F), (∀ i, evI F (y i) = 0) → Dense.pt x 0 + y = Dense.pt x (Box.fn y) := fun x y hy => by
      rw [← Box.pt_self (Dense.pt x 0 + y), Box.nf_add, Box.nf_pt, show Box.nf y = 0 from funext hy, add_zero]
      exact congrArg (Dense.pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (Dense.pt 0 (Box.fn z) i) = 0 := fun i => congrFun (Dense.evI_pt 0 (Box.fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (Dense.pt (Box.nf z) 0) (Box.at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show Box.fn (Dense.pt 0 (Box.fn z)) = Box.fn z from rfl, Box.pt_self] at this
    obtain ⟨f, e⟩ := Box.slice Ψ.2.1 (Box.fn y)
    have g : Box.Gs d.dd.e d.B.emb ε θ θ' f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (Dense.pt x (Box.fn y))
      rwa [Pi.smul_apply, Box.D, Box.D, Box.DP_pt e, Box.DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show Box.nf y = 0 from funext (s1 y hy), Box.pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← Box.actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← Box.actB_inv k u, ← Box.actB_inv k u', ← om_D k (Box.at_actB _ a) h.1, ← om_D k (Box.at_actB _ b) h.1,
      ← map_smul]
    refine congrArg (d.om k) (h.2.2 _ _ (Box.at_actB _ a) (Box.at_actB _ b) fun w => ?_)
    have cm := (hc k⁻¹ (inv_mem hk) w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm

end PositivityTheory.SiegelWeilFormula.KK

end
end

