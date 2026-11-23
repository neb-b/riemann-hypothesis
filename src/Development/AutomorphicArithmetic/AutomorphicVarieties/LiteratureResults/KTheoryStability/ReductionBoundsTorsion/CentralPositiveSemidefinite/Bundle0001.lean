module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.TSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.LamSApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.ActLEqOfScalar
section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

theorem scalar_conj {N : ℕ} (c : ℂ) (hc : c ≠ 0) (M : Matrix (Fin N) (Fin N) ℂ) :
    ((Matrix.scalar (Fin N) c)⁻¹)ᴴ * M * (Matrix.scalar (Fin N) c)⁻¹ =
      (((‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) • M := by
  have hinv : (Matrix.scalar (Fin N) c)⁻¹ = (c⁻¹) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.scalar_apply, smul_mul_assoc, one_mul, ← Matrix.diagonal_smul]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hc]
  rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul]
  congr 1
  rw [star_inv₀, ← mul_inv, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem mat_actL_scalar (g : Gp L N) (c : InfinitePlace L → ℂ) (hc : ∀ w, c w ≠ 0)
    (hg : ∀ w, ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (c w))
    (h : HS L N) (w : InfinitePlace L) :
    mat (actL g h) w = (((‖c w‖ ^ 2)⁻¹ : ℝ) : ℂ) • mat h w := by
  unfold actL actM
  simp only [LinearMap.coe_toContinuousLinearMap', coe_units_inv, LinearMap.coe_mk, AddHom.coe_mk,
    mat_mkHS]
  rw [hg w]
  exact scalar_conj (c w) (hc w) _

theorem actL_eq_of_scalar (g g' : Gp L N) (c c' : InfinitePlace L → ℂ) (hc : ∀ w, c w ≠ 0)
    (hc' : ∀ w, c' w ≠ 0)
    (hg : ∀ w, ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (c w))
    (hg' : ∀ w, ((g' w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (c' w))
    (hn : ∀ w, ‖c w‖ = ‖c' w‖) : actL g = actL g' := by
  ext1 h
  exact HS_ext fun w => by rw [mat_actL_scalar g c hc hg, mat_actL_scalar g' c' hc' hg', hn]

omit [NumberField L] in
theorem scal_coe (s : InfinitePlace L → ℂˣ) (w : InfinitePlace L) :
    ((scal L N s w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (s w : ℂ) := by
  simp [scal]

omit [NumberField L] in
theorem sc_coe (t : InfinitePlace L → ℝ) (w : InfinitePlace L) :
    (((sc t : Gp L N) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.scalar (Fin N) ((Real.exp (t w) : ℝ) : ℂ) := by
  simp [sc, scal]

omit [NumberField L] in
theorem emb_scalar_coe (u : (𝓞 L)ˣ) (w : InfinitePlace L) :
    ((emb L N (GeneralLinearGroup.scalar (Fin N) u) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.scalar (Fin N) (w.embedding ((u : 𝓞 L) : L)) := by
  ext i j
  simp [emb, toP, toK, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem exp_ne (x : ℝ) : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'

theorem tScal : TScal := by
  unfold TScal
  intro L _ _ N
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t t'
    funext w
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, sc_coe, Pi.add_apply, Real.exp_add, Complex.ofReal_mul,
      map_mul]
  · intro t x
    funext w
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, sc_coe]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  · intro u
    have hx : ((u : 𝓞 L) : L) ≠ 0 := by simp
    refine actL_eq_of_scalar _ _ (fun w => w.embedding ((u : 𝓞 L) : L))
      (fun w => ((Real.exp (lg u w) : ℝ) : ℂ)) (fun w => (map_ne_zero _).2 hx) (fun w => exp_ne _)
      (emb_scalar_coe u) (fun w => sc_coe _ w) (fun w => ?_)
    rw [InfinitePlace.norm_embedding_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), lg, Real.exp_log (w.pos_iff.2 hx)]
  · intro s
    refine actL_eq_of_scalar _ _ (fun w => (s w : ℂ)) (fun w => ((Real.exp (Real.log ‖(s w : ℂ)‖) : ℝ) : ℂ))
      (fun w => (s w).ne_zero) (fun w => exp_ne _) (scal_coe s) (fun w => sc_coe _ w) (fun w => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.exp_log (norm_pos_iff.2 (s w).ne_zero)]
  · have key : ∀ (t : InfinitePlace L → ℝ) (h : HS L N) w i j,
        ((actL (sc t) h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) w i j =
          (((‖((Real.exp (t w) : ℝ) : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) *
            (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j := by
      intro t h w i j
      exact congrFun (congrFun (mat_actL_scalar (sc t) (fun w => ((Real.exp (t w) : ℝ) : ℂ))
        (fun w => exp_ne _) (fun w => sc_coe t w) h w) i) j
    rw [continuous_clm_apply]
    intro h
    apply continuous_induced_rng.2
    refine continuous_pi fun w => continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, key]
    refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
    refine Continuous.inv₀ (by fun_prop) fun t => pow_ne_zero _ (norm_ne_zero_iff.2 (exp_ne _))

end PositivityTheory.KB.CentralizerFixed

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.AvCongr
section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem pb_congr {q : ℕ} {g g' : Gp L N} (e : actL g = actL g') (ω : Form (HS L N) q) :
    pb g ω = pb g' ω := by
  unfold pb
  rw [e]

theorem pb_mul {q : ℕ} (g g' : Gp L N) (ω : Form (HS L N) q) (h : HS L N) :
    pb (g * g') ω h = (pb g ω (actL g' h)).compContinuousLinearMap (actL g') := by
  have e : actL (g * g') = (actL g).comp (actL g') := by
    ext1 x
    exact actL_mul g g' x
  unfold pb
  rw [e]
  ext m
  rfl

theorem pb_one {q : ℕ} (ω : Form (HS L N) q) (h : HS L N) : pb 1 ω h = ω h := by
  have e : actL (1 : Gp L N) = ContinuousLinearMap.id ℝ (HS L N) := by
    ext1 x
    exact actL_one x
  unfold pb
  rw [e]
  ext m
  rfl

theorem sc_zero (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') :
    (sc 0 : Gp L N) = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := (sc 0 : Gp L N)) (this.symm.trans (mul_one _).symm)

theorem fix_zero {q : ℕ} {ω : Form (HS L N) q}
    (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') : (0 : InfinitePlace L → ℝ) ∈ Fix ω := by
  intro h _
  rw [sc_zero hadd]
  exact pb_one ω h

theorem fix_add {q : ℕ} {ω : Form (HS L N) q}
    (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') {t t' : InfinitePlace L → ℝ}
    (ht : t ∈ Fix ω) (ht' : t' ∈ Fix ω) : t + t' ∈ Fix ω := by
  intro h hh
  have e := ht (actL (sc t') h) (actL_pos _ hh)
  rw [hadd, pb_mul, e]
  exact ht' h hh

theorem av_congr {q : ℕ} (v : InfinitePlace L → ℝ) {ω ω' : Form (HS L N) q}
    (e : ∀ h ∈ Pos L N, ω h = ω' h) : ∀ h ∈ Pos L N, av v ω h = av v ω' h := by
  intro h hh
  show (∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω h) = ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω' h
  congr 1
  funext τ
  show (ω (actL _ h)).compContinuousLinearMap _ = (ω' (actL _ h)).compContinuousLinearMap _
  rw [e _ (actL_pos _ hh)]

theorem inv_av (hA : TAv) {q : ℕ} (v : InfinitePlace L → ℝ) {ω : Form (HS L N) q}
    (hc : ContinuousOn ω (Pos L N)) {g : Gp L N} (hg : ∀ t, sc t * g = g * sc t) (hinv : FInv ω g) :
    FInv (av v ω) g := by
  intro h hh
  have := (hA L N q v ω hc).2.1 g hg h hh
  change pb g (av v ω) h = _
  rw [this]
  exact av_congr v (fun k hk => hinv k hk) h hh

theorem sc_cont (v : InfinitePlace L → ℝ) : Continuous fun τ : ℝ => (sc (τ • v) : Gp L N) := by
  refine continuous_pi fun w => ?_
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun τ : ℝ => Matrix.scalar (Fin N) ((Real.exp ((τ • v) w) : ℂ))
    simp only [Matrix.scalar_apply, Pi.smul_apply, smul_eq_mul]
    refine Continuous.matrix_diagonal (continuous_pi fun _ => ?_)
    fun_prop
  · show Continuous fun τ : ℝ => Matrix.scalar (Fin N) (((Real.exp ((τ • v) w) : ℂ))⁻¹)
    simp only [Matrix.scalar_apply, Pi.smul_apply, smul_eq_mul]
    refine Continuous.matrix_diagonal (continuous_pi fun _ => ?_)
    refine Continuous.inv₀ (by fun_prop) (fun τ => ?_)
    exact_mod_cast (Real.exp_pos _).ne'

def Carr {k : ℕ} (ω₀ : Form (HS L N) (k + 1)) (B : Gp L N → ℝ) (ω : Form (HS L N) (k + 1)) : Prop :=
  ContinuousOn ω (Pos L N) ∧ dC (intP ω) = 0 ∧ (∀ γ, FInv ω (emb L N γ)) ∧
    (∀ c : ℝ, (fun _ => c) ∈ Fix ω) ∧
    (∀ z : Chn (Gm L N) (k + 1), IsCyc z →
      ev (emb L N) (intP ω) (one L N) z = ev (emb L N) (intP ω₀) (one L N) z) ∧
    ∃ C, 0 ≤ C ∧ ∀ x, ‖fr ω x‖ ≤ C * B x

theorem step_dC (hA : TAv) {k : ℕ} {ω : Form (HS L N) (k + 1)} (hc : ContinuousOn ω (Pos L N))
    (hd : dC (intP ω) = 0) (v : InfinitePlace L → ℝ) : dC (intP (av v ω)) = 0 := by
  funext y
  obtain ⟨_, _, _, hcont, hint, _⟩ := hA L N (k+1) v ω hc
  have e : dC (intP (av v ω)) y = ∫ τ in (0:ℝ)..1, dC (intP ω) (fun j => (sc (τ • v) : Gp L N) • y j) := by
    simp only [dC, hint]
    rw [intervalIntegral.integral_finsetSum]
    · congr 1
      funext i
      rw [intervalIntegral.integral_const_mul]
    · intro i _
      exact ((hcont _).const_mul _).intervalIntegrable _ _
  rw [e, hd]
  simp

theorem step_ev (hEv : SEv) (hSc : TScal) (hSi : TSimp) (hA : TAv) {k : ℕ} {ω : Form (HS L N) (k + 1)}
    (hc : ContinuousOn ω (Pos L N)) (hd : dC (intP ω) = 0) (hΓ : ∀ γ, FInv ω (emb L N γ))
    (v : InfinitePlace L → ℝ) (z : Chn (Gm L N) (k + 1)) (hz : IsCyc z) :
    ev (emb L N) (intP (av v ω)) (one L N) z = ev (emb L N) (intP ω) (one L N) z := by
  obtain ⟨_, _, _, hcont, hint, _⟩ := hA L N (k+1) v ω hc
  have hcomm := (hSc L N).2.1
  have hinvF : Inv (emb L N) (intP ω) := fun γ y => (hSi L N (k+1)).2 ω _ (hΓ γ) y
  have hcst := (hEv (Gm L N) (Gp L N) (Pos L N) (emb L N) k (intP ω) hinvF hd).2
  have key : ∀ τ : ℝ, (z.sum fun g r => r * intP ω (fun j => (sc (τ • v) : Gp L N) • (emb L N (Fin.partialProd g j) • one L N)))
      = ev (emb L N) (intP ω) (one L N) z := by
    intro τ
    rw [← hcst ((sc (τ • v) : Gp L N) • one L N) (one L N) z hz]
    simp only [ev]
    refine Finsupp.sum_congr fun g _ => ?_
    congr 2
    funext j
    rw [smul_smul, smul_smul, hcomm]
  show (z.sum fun g r => r * intP (av v ω) (fun j => emb L N (Fin.partialProd g j) • one L N)) = _
  simp only [hint]
  have e : (z.sum fun g r => r * ∫ τ in (0:ℝ)..1, intP ω (fun j => (sc (τ • v) : Gp L N) • (emb L N (Fin.partialProd g j) • one L N)))
      = ∫ τ in (0:ℝ)..1, z.sum fun g r => r * intP ω (fun j => (sc (τ • v) : Gp L N) • (emb L N (Fin.partialProd g j) • one L N)) := by
    simp only [Finsupp.sum]
    rw [intervalIntegral.integral_finsetSum]
    · congr 1
      funext g
      rw [intervalIntegral.integral_const_mul]
    · intro g _
      exact ((hcont _).const_mul _).intervalIntegrable _ _
  rw [e]
  simp only [key]
  simp

theorem step_bd (hSc : TScal) (hA : TAv) {k : ℕ} {ω : Form (HS L N) (k + 1)} (hc : ContinuousOn ω (Pos L N))
    {B : Gp L N → ℝ} (hB : ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x)
    (hB0 : ∀ x, 0 ≤ B x) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖fr ω x‖ ≤ C * B x) (v : InfinitePlace L → ℝ) :
    ∃ C', 0 ≤ C' ∧ ∀ x, ‖fr (av v ω) x‖ ≤ C' * B x := by
  obtain ⟨-, hcomm, -, -, -⟩ := hSc L N
  obtain ⟨-, -, -, -, -, hAfr⟩ := hA L N (k + 1) v ω hc
  obtain ⟨CK, hCK⟩ := hB _ ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (sc_cont (N := N) v))
  refine ⟨C * max CK 0, mul_nonneg hC0 (le_max_right _ _), fun x => ?_⟩
  rw [hAfr x]
  have hb : ∀ τ ∈ Set.uIoc (0 : ℝ) 1, ‖fr ω (sc (τ • v) * x)‖ ≤ C * max CK 0 * B x := fun τ hτ => by
    rw [Set.uIoc_of_le zero_le_one] at hτ
    rw [hcomm]
    calc ‖fr ω (x * sc (τ • v))‖ ≤ C * B (x * sc (τ • v)) := hC _
      _ ≤ C * (max CK 0 * B x) := mul_le_mul_of_nonneg_left
          ((hCK _ ⟨τ, ⟨hτ.1.le, hτ.2⟩, rfl⟩ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hB0 x))) hC0
      _ = C * max CK 0 * B x := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

theorem step (hEv : SEv) (hSc : TScal) (hSi : TSimp) (hA : TAv) {k : ℕ} {ω₀ ω : Form (HS L N) (k + 1)}
    {B : Gp L N → ℝ} (hB : ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x)
    (hB0 : ∀ x, 0 ≤ B x) (hω : Carr ω₀ B ω) (v : InfinitePlace L → ℝ) (hv : v ∈ Fix ω) :
    Carr ω₀ B (av v ω) ∧ (∀ t ∈ Fix ω, t ∈ Fix (av v ω)) ∧ ∀ σ : ℝ, σ • v ∈ Fix (av v ω) := by
  obtain ⟨hc, hd, hΓ, hdiag, hev, C, hC0, hC⟩ := hω
  obtain ⟨-, hcomm, -, -, -⟩ := hSc L N
  have hfix : ∀ t ∈ Fix ω, t ∈ Fix (av v ω) := fun t ht =>
    inv_av hA v hc (fun t' => hcomm t' (sc t)) ht
  have hper := ((hA L N (k + 1) v ω hc).2.2.1 hv)
  have hAc := (hA L N (k + 1) v ω hc).1
  exact ⟨⟨hAc, step_dC hA hc hd v, fun γ => inv_av hA v hc (fun t => hcomm t _) (hΓ γ),
    fun c => hfix _ (hdiag c), fun z hz => (step_ev hEv hSc hSi hA hc hd hΓ v z hz).trans (hev z hz),
    step_bd hSc hA hc hB hB0 hC0 hC v⟩, hfix, hper⟩

theorem iter (hEv : SEv) (hSc : TScal) (hSi : TSimp) (hA : TAv) {k : ℕ} {ω₀ ω : Form (HS L N) (k + 1)}
    {B : Gp L N → ℝ} (hB : ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x)
    (hB0 : ∀ x, 0 ≤ B x) (hω : Carr ω₀ B ω) (l : List (𝓞 L)ˣ) :
    ∃ ω', Carr ω₀ B ω' ∧ ∀ u ∈ l, ∀ σ : ℝ, σ • lg u ∈ Fix ω' := by
  induction l with
  | nil => exact ⟨ω, hω, by simp⟩
  | cons u l ih =>
    obtain ⟨ω1, h1, hl1⟩ := ih
    obtain ⟨-, -, hemb, -, -⟩ := hSc L N
    have hu : lg u ∈ Fix ω1 := by
      intro h hh
      rw [pb_congr (hemb u).symm]
      exact h1.2.2.1 _ h hh
    obtain ⟨h2, hfix, hper⟩ := step hEv hSc hSi hA hB hB0 h1 (lg u) hu
    refine ⟨av (lg u) ω1, h2, fun u' hu' σ => ?_⟩
    rcases List.mem_cons.1 hu' with rfl | hu'
    · exact hper σ
    · exact hfix _ (hl1 u' hu' σ)

theorem join (hSp : TSpan) (hSc : TScal) (hSi : TSimp) (hA : TAv) (hEv : SEv) : SCen := by
  intro L _ _ N k ω hG hΓ hS B hB hfr
  have hB0 : ∀ x, 0 ≤ B x := fun x => (norm_nonneg _).trans (hfr x)
  obtain ⟨l, hl⟩ := hSp L
  have h0 : Carr ω B ω := ⟨hG.1, hG.2, hΓ,
    fun c => hS (fun _ => Units.mk0 ((Real.exp c : ℝ) : ℂ) (by exact_mod_cast (Real.exp_pos c).ne'))
      (fun _ _ => rfl),
    fun _ _ => rfl, 1, zero_le_one, fun x => by simpa using hfr x⟩
  obtain ⟨ω', ⟨hc, hd, hΓ', hdiag, hev, C, -, hC⟩, hlf⟩ := iter hEv hSc hSi hA hB hB0 h0 l
  obtain ⟨hadd, -, -, hscal, -⟩ := hSc L N
  have key : ∀ t ∈ Submodule.span ℝ (insert (fun _ => (1 : ℝ)) {x | ∃ u ∈ l, lg u = x}),
      ∀ σ : ℝ, σ • t ∈ Fix ω' := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨u, hu, rfl⟩
      · intro σ
        convert hdiag σ using 1 <;> ext w <;> simp
      · exact hlf u hu
    | zero => intro σ; rw [smul_zero]; exact fix_zero hadd
    | add x y _ _ hx hy => intro σ; rw [smul_add]; exact fix_add hadd (hx σ) (hy σ)
    | smul a x _ hx => intro σ; rw [smul_smul]; exact hx _
  refine ⟨ω', ⟨hc, hd⟩, hΓ', fun s => ?_, hev, C, hC⟩
  intro h hh
  have := key _ (hl (fun w => Real.log ‖(s w : ℂ)‖)) 1 h hh
  rw [one_smul] at this
  change pb (scal L N s) ω' h = ω' h
  rw [pb_congr (hscal s)]
  exact this

end PositivityTheory.KB.CentralizerFixed

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.RealSmulPosSemidef
section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

open ComplexOrder in
theorem real_smul_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosDef) {a : ℝ} (ha : 0 < a) :
    (a • M).PosDef := by
  have e : a • M = (a : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [e]
  exact h.smul (Complex.zero_lt_real.2 ha)

open ComplexOrder in
theorem real_smul_posSemidef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) : (a • M).PosSemidef := by
  have e : a • M = (a : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [e]
  exact h.smul (Complex.zero_le_real.2 ha)

open ComplexOrder in
theorem pos_convex (L : Type) [Field L] [NumberField L] (N : ℕ) : Convex ℝ (Pos L N) := by
  intro x hx y hy a b ha hb hab w
  have e : mat (a • x + b • y) w = a • mat x w + b • mat y w := by simp
  change (mat (a • x + b • y) w).PosDef
  rw [e]
  rcases ha.lt_or_eq with ha' | ha'
  · exact (real_smul_posDef (hx w) ha').add_posSemidef (real_smul_posSemidef (hy w).posSemidef hb)
  · have hb1 : b = 1 := by linarith
    rw [← ha', hb1, zero_smul, zero_add, one_smul]
    exact hy w

theorem simplex_meas (q : ℕ) :
    MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  refine IsClosed.measurableSet ?_
  refine (IsClosed.inter ?_ ?_ : IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1}))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const

theorem simplex_mem {L : Type} [Field L] [NumberField L] {N q : ℕ} (y : Fin (q + 1) → Pos L N)
    (t : Fin q → ℝ) (h0 : ∀ j, 0 ≤ t j) (h1 : ∑ j, t j ≤ 1) :
    (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) ∈ Pos L N := by
  let c : Fin (q + 1) → ℝ := Fin.cons (1 - ∑ j, t j) t
  have e : (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) = ∑ i, c i • (y i).1 := by
    rw [Fin.sum_univ_succ]
    simp only [c, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      sub_smul, one_smul]
    abel
  rw [e]
  refine (pos_convex L N).sum_mem (fun i _ => ?_) ?_ (fun i _ => (y i).2)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [c, Fin.cons_zero]; linarith
    · simp only [c, Fin.cons_succ]; exact h0 j
  · rw [Fin.sum_univ_succ]
    simp only [c, Fin.cons_zero, Fin.cons_succ]
    ring

theorem tSimp : TSimp := by
  intro L _ _ N q
  refine ⟨fun y t h0 h1 => simplex_mem y t h0 h1, fun ω g hg y => ?_⟩
  unfold intP intS
  refine setIntegral_congr_fun (simplex_meas q) fun t ht => ?_
  have hp := simplex_mem y t ht.1 ht.2
  have := congrArg (fun f => f fun j => (y j.succ).1 - (y 0).1) (hg _ hp)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at this
  rw [← this]
  have hs : ∀ k : Pos L N, (g • k).1 = actL g k.1 := fun k => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hs, map_add (f := _), map_sum, map_smul, map_sub]
  congr 1
  funext j
  simp [map_sub]

end PositivityTheory.KB.CentralizerFixed

end
end

