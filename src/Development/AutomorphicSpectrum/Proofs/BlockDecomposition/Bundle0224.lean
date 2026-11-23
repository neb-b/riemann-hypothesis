module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableField
section
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeStable

theorem secondCountable_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := by
  intro h0
  exact (irreducible_uniformizer F).ne_zero (Subtype.ext h0)


variable (F) in
def scal (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    have h := unif_ne_zero (F := F)
    rw [smul_mul_smul_comm, one_mul, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_smul]
  inv_val := by
    have h := unif_ne_zero (F := F)
    rw [smul_mul_smul_comm, one_mul, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_smul]

theorem scal_mulVec (m M : ℕ) (x : Fin m → F) :
    ((scal F m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x = ((uniformizer F : F)⁻¹ ^ M) • x := by
  change (((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)) *ᵥ x = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem image_scal (m M : ℕ) :
    (fun x => ((scal F m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 = lat F m M := by
  have h := unif_ne_zero (F := F)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hxi := hx i
    rw [pow_zero, one_mul] at hxi
    simp only [scal_mulVec m M x, Pi.smul_apply, smul_eq_mul]
    rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_mul]
  · intro hy
    refine ⟨fun i => (uniformizer F : F) ^ M * y i, fun i => ?_, ?_⟩
    · rw [pow_zero, one_mul]; exact hy i
    · funext i
      simp only [scal_mulVec m M _, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_mul]

theorem div_scal_inv {m c M : ℕ} (hM : c ≤ M) :
    Div c (((scal F m M)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  intro i j
  refine ⟨(uniformizer F : F) ^ (M - c) * (1 : Matrix (Fin m) (Fin m) F) i j, ?_, ?_⟩
  · refine mul_mem (pow_mem (uniformizer F).2 _) ?_
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · change (((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)) i j = _
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hM]

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
  (ψ : AddChar F ℂ) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin n) F) V) (k : ℕ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def avg (M : ℕ) (u' u : V) : ℂ :=
  ∫ x in lat F (k + 1) M, ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u) ∂(Measure.pi fun _ => μ)

theorem exists_char (hψ : Continuous ψ) (hlat : ∀ M, IsCompact (lat F (k + 1) M))
    (hcont : ∀ u u', Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)))
    (hst : ∀ u u', ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → avg μ ψ ρ k B M u' u = avg μ ψ ρ k B M₀ u' u) :
    ∃ B', Char μ ρ ψ k B B' := by
  haveI := secondCountable_field F
  choose m hm using hst
  have hint : ∀ M u' u, IntegrableOn
      (fun x : Fin (k + 1) → F => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)) (lat F (k + 1) M)
      (Measure.pi fun _ => μ) := by
    intro M u' u
    refine ContinuousOn.integrableOn_compact (hlat M) (Continuous.continuousOn ?_)
    exact (hψ.comp (continuous_apply _).neg).mul (hcont u u')
  let f : V → V → ℂ := fun u' u => avg μ ψ ρ k B (m u u') u' u
  have hf : ∀ u' u M, m u u' ≤ M → f u' u = avg μ ψ ρ k B M u' u :=
    fun u' u M h => (hm u u' M h).symm
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) f ?_ ?_ ?_ ?_, ?_⟩
  · intro a b w
    let M := max (m w (a + b)) (max (m w a) (m w b))
    rw [hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)),
      hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [avg]
    rw [← integral_add (hint M a w) (hint M b w)]
    congr 1
    funext x
    simp [mul_add]
  · intro c a w
    let M := max (m w (c • a)) (m w a)
    rw [hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]
    simp only [avg]
    rw [smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp
    ring
  · intro a v w
    let M := max (m (v + w) a) (max (m v a) (m w a))
    rw [hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)),
      hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [avg]
    rw [← integral_add (hint M a v) (hint M a w)]
    congr 1
    funext x
    simp [mul_add]
  · intro c a v
    let M := max (m (c • v) a) (m v a)
    rw [hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]
    simp only [avg]
    rw [smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp
    ring
  · intro u u'
    exact ⟨m u u', fun M hM => hf u' u M hM⟩

theorem stable_average : L0 → FormCoefficientStability → StableAverageExists := by
  intro h0 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hInv
  obtain ⟨hψc, hL⟩ := h0 F μ ψ hψ
  have h4' := h4 F μ ψ hψ n V ρ hρ l k B hk hInv
  refine exists_char μ ψ ρ k B hψc (fun M => ((hL (k + 1)).1 M).1) (fun u u' => (h4' u u').1) ?_
  intro u u'
  obtain ⟨c, hc⟩ := (h4' u u').2
  refine ⟨c + 1, fun M hM => ?_⟩
  have := hc (scal F (k + 1) M) (div_scal_inv hM)
  rw [image_scal] at this
  exact this

end GlobalTheory.CompanionTheory.SatakeStable

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
section
noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.SecBd

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem val_mem (y : G n) : y.val ∈ GLs n := (Matrix.isUnits_det_units y).ne_zero

theorem basis_true_eq_single (a c : Fin n) : bs (true, a, c) = Matrix.single a c (1 : ℂ) := by simp [bs]

theorem bs_f (a c : Fin n) : bs (false, a, c) = Matrix.single a c Complex.I := by simp [bs]

theorem Rw_append {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × Fin n × Fin n))
    (p : Bool × Fin n × Fin n) (f : Mat n → V) : Rw (w ++ [p]) f = Rw w (Rd (bs p) f) := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    show Rd (bs q) (Rw (w ++ [p]) f) = Rd (bs q) (Rw w (Rd (bs p) f))
    rw [ih]

theorem Rd_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X - X') f g = Rd X f g - Rd X' f g := by
  simp [Rd, mul_sub]

theorem Rd_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X + X') f g = Rd X f g + Rd X' f g := by
  simp [Rd, mul_add]

theorem single_conj (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]

theorem skewY (a c : Fin n) :
    (Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ) : Mat n)ᴴ = -(Matrix.single a c (1 : ℂ) - Matrix.single c a 1) := by
  simp [Matrix.conjTranspose_sub, single_conj]

theorem skewZ (a c : Fin n) :
    (Matrix.single a c Complex.I + Matrix.single c a Complex.I : Mat n)ᴴ =
      -(Matrix.single a c Complex.I + Matrix.single c a Complex.I) := by
  simp [Matrix.conjTranspose_add, single_conj, Matrix.single_neg, add_comm]

section L2

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem cls_eq {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = h.toLp _ := dif_pos h

theorem cls_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f =ᵐ[μ] fun y => f y.val := by
  rw [cls_eq μ h]
  exact h.coeFn_toLp

theorem cls_congr {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (e : ∀ g ∈ GLs n, f g = f' g) :
    cls μ f = cls μ f' := by
  have e' : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => e _ (val_mem y)
  have h' : MemLp (fun y : G n => f' y.val) 2 μ := e' ▸ h
  rw [cls_eq μ h, cls_eq μ h']
  exact MemLp.toLp_congr h h' (by rw [e'])

theorem cls_sub {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (h' : MemLp (fun y : G n => f' y.val) 2 μ) :
    cls μ (fun g => f g - f' g) = cls μ f - cls μ f' := by
  rw [cls_eq μ h, cls_eq μ h', cls_eq μ (h.sub h')]
  exact MemLp.toLp_sub h h'

theorem cls_sum {ι : Type} (s : Finset ι) (F : ι → Mat n → V)
    (h : ∀ i ∈ s, MemLp (fun y : G n => F i y.val) 2 μ) :
    MemLp (fun y : G n => ∑ i ∈ s, F i y.val) 2 μ ∧ cls μ (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, cls μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : MemLp (fun _ : G n => (0 : V)) 2 μ := MemLp.zero
    refine ⟨by simpa using h0, ?_⟩
    simp only [Finset.sum_empty]
    rw [cls_eq μ h0]
    exact MemLp.toLp_zero h0
  | insert i s hi ih =>
    obtain ⟨m, e⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hi' := h i (Finset.mem_insert_self i s)
    simp only [Finset.sum_insert hi]
    refine ⟨hi'.add m, ?_⟩
    rw [← e, cls_eq μ hi', cls_eq μ (f := fun g => ∑ i ∈ s, F i g) m,
      cls_eq μ (f := fun g => F i g + ∑ i ∈ s, F i g) (hi'.add m)]
    exact MemLp.toLp_add hi' m

theorem norm_le_of_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (x : Lp V 2 μ) (C : V →L[ℂ] V)
    (e : ∀ᵐ y ∂μ, x y = C (f (y : G n).val)) : ‖x‖ ≤ ‖C‖ * ‖cls μ f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [e, cls_ae μ h] with y h1 h2
  rw [h1, h2]
  exact C.le_opNorm _

end L2

theorem pol_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    -(⟪v, u⟫_ℂ).re ≤ ‖u - v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u + v‖]

theorem pol_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    (⟪v, u⟫_ℂ).re ≤ ‖u + v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u - v‖]

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Rd (hR : RCalc) {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) : Sob μ (Rd (bs p) f) :=
  ⟨((hR n).1 V f hS.1).1 _, fun w => by
    have := hS.2 (w ++ [p])
    rwa [Rw_append] at this⟩

theorem mem1 {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) :
    MemLp (fun y : G n => Rd (bs p) f y.val) 2 μ := hS.2 [p]

theorem mem0 {f : Mat n → V} (hS : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hS.2 []

end Main

theorem secBound (hI : IbpSob) : SecBound := by
  intro n _ _ μ _ E hL hU hR
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewZ a c)
  refine ⟨∑ a, ∑ c, (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4, fun f hS hsec => ?_⟩
  have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
  set x := cls μ f with hx
  have hf0 := mem0 μ hS

  have hd : ∀ p q : Bool × Fin n × Fin n, MemLp (fun y : G n => Rd (bs p) (Rd (bs q) f) y.val) 2 μ := fun p q =>
    mem1 μ (sob_Rd μ hR hS q) p
  have hip : ∀ p q : Bool × Fin n × Fin n, ⟪cls μ (Rd (bs p) (Rd (bs q) f)), x⟫_ℂ =
      -⟪cls μ (Rd (bs q) f), cls μ (Rd (bs p) f)⟫_ℂ := fun p q =>
    hI n μ E.V hL hU hR _ _ (sob_Rd μ hR hS q) hS (bs p)

  let T : Fin n → Fin n → Mat n → E.V := fun a c g =>
    Rd (bs (true, a, c)) (Rd (bs (true, c, a)) f) g - Rd (bs (false, a, c)) (Rd (bs (false, c, a)) f) g
  have hT : ∀ a c, MemLp (fun y : G n => T a c y.val) 2 μ := fun a c => (hd _ _).sub (hd _ _)
  have hOm : ∀ g ∈ GLs n, Om f g = ∑ a, ∑ c, T a c g := by
    intro g hg
    rw [GlobalTheory.CompanionTheory.Casimir.omFormula n E.V f hS.1 g hg]
    simp only [T, basis_true_eq_single, bs_f]
  have hsumc : ∀ a, MemLp (fun y : G n => ∑ c, T a c y.val) 2 μ ∧
      cls μ (fun g => ∑ c, T a c g) = ∑ c, cls μ (T a c) := fun a =>
    cls_sum μ _ (T a) fun c _ => hT a c
  have hsum := cls_sum μ Finset.univ (fun a g => ∑ c, T a c g) fun a _ => (hsumc a).1
  have hcls : cls μ (Om f) = ∑ a, ∑ c, cls μ (T a c) := by
    have h1 : cls μ (fun g => ∑ a, ∑ c, T a c g) = cls μ (Om f) :=
      cls_congr μ hsum.1 fun g hg => (hOm g hg).symm
    rw [← h1, hsum.2]
    exact Finset.sum_congr rfl fun a _ => (hsumc a).2

  have hterm : ∀ a c, (⟪cls μ (T a c), x⟫_ℂ).re ≤ (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4 * ‖x‖ ^ 2 := by
    intro a c
    set u := cls μ (Rd (bs (true, a, c)) f) with hu
    set u' := cls μ (Rd (bs (true, c, a)) f) with hu'
    set v := cls μ (Rd (bs (false, a, c)) f) with hv
    set v' := cls μ (Rd (bs (false, c, a)) f) with hv'
    have e1 : (⟪cls μ (T a c), x⟫_ℂ).re = -(⟪u', u⟫_ℂ).re + (⟪v', v⟫_ℂ).re := by
      have : cls μ (T a c) = _ := cls_sub μ (hd (true, a, c) (true, c, a)) (hd (false, a, c) (false, c, a))
      rw [this, inner_sub_left, hip, hip]
      simp [hu, hu', hv, hv']
    have b1 : ‖u - u'‖ ≤ ‖BY a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_sub u u', cls_ae μ (mem1 μ hS (true, a, c)), cls_ae μ (mem1 μ hS (true, c, a))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ← hBY a c f hCE _ (val_mem y), Rd_sub, basis_true_eq_single, basis_true_eq_single]
    have b2 : ‖v + v'‖ ≤ ‖BZ a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_add v v', cls_ae μ (mem1 μ hS (false, a, c)), cls_ae μ (mem1 μ hS (false, c, a))] with y h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, ← hBZ a c f hCE _ (val_mem y), Rd_add, bs_f, bs_f]
    have p1 := pol_sub u u'
    have p2 := pol_add v v'
    have s1 : ‖u - u'‖ ^ 2 ≤ (‖BY a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b1 2
    have s2 : ‖v + v'‖ ^ 2 ≤ (‖BZ a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b2 2
    rw [e1]
    nlinarith
  rw [hcls, sum_inner, Complex.re_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sum_inner, Complex.re_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun c _ => hterm a c

theorem secBound_main : SecBound := secBound _root_.GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob

end GlobalTheory.CompanionTheory.SecBd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSequenceUniformCauchy
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.RwCauchy

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem Rw_sub_on {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b : Mat n → V}
    (ha : ContDiffOn ℝ ∞ a (GLs n)) (hb : ContDiffOn ℝ ∞ b (GLs n))
    (w : List (Bool × Fin n × Fin n)) :
    ∀ z ∈ GLs n, Rw w (a - b) z = Rw w a z - Rw w b z := by
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    have h1 : Rw (p :: w) (a - b) z = Rd (bs p) (Rw w a - Rw w b) z :=
      Rd_congr (f := Rw w (a - b)) (f' := Rw w a - Rw w b) (fun y hy => ih y hy) (bs p) z hz
    rw [h1]
    have hU := isOpen_GLs.mem_nhds hz
    have da : DifferentiableAt ℝ (Rw w a) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' ha w).contDiffAt hU).differentiableAt (by simp)
    have db : DifferentiableAt ℝ (Rw w b) z :=
      ((GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hb w).contDiffAt hU).differentiableAt (by simp)
    show fderiv ℝ (Rw w a - Rw w b) z (z * bs p) =
      fderiv ℝ (Rw w a) z (z * bs p) - fderiv ℝ (Rw w b) z (z * bs p)
    have e := (da.hasFDerivAt.sub db.hasFDerivAt).fderiv
    exact DFunLike.congr_fun e (z * bs p)

theorem uniformCauchy : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ) → (∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) → ∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n) := by
  intro hS n _ _ μ _ V _ _ _ g x hg hm hc w
  obtain ⟨S, C, hC, hsup⟩ := GlobalTheory.CompanionTheory.PresSobA.SupG.sup_sq_bound hS n μ
  have hbound : ∀ k l, ∀ z ∈ GLs n, ‖Rw w (g k) z - Rw w (g l) z‖ ^ 2 ≤
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l))‖ ^ 2 := by
    intro k l z hz
    have sk := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
    have sl := GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg l) w
    have key : ∀ w', ∀ y ∈ GLs n, Rw w' (Rw w (g k) - Rw w (g l)) y =
        Rw (w' ++ w) (g k) y - Rw (w' ++ w) (g l) y := by
      intro w' y hy
      rw [Rw_sub_on sk sl w' y hy, Rw_append, Rw_append]
    have hcl : ∀ w', MemLp (fun y : G n => Rw w' (Rw w (g k) - Rw w (g l)) y.val) 2 μ ∧
        cls μ (Rw w' (Rw w (g k) - Rw w (g l))) =
          cls μ (Rw (w' ++ w) (g k)) - cls μ (Rw (w' ++ w) (g l)) := by
      intro w'
      refine cls_of_ae μ ?_
      filter_upwards [Lp.coeFn_sub (cls μ (Rw (w' ++ w) (g k))) (cls μ (Rw (w' ++ w) (g l))),
        coe_cls μ (hm k (w' ++ w)), coe_cls μ (hm l (w' ++ w))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, key w' _ (val_mem_GLs y)]
    have := hsup V (Rw w (g k) - Rw w (g l)) (sk.sub sl) (fun w' => (hcl w').1) z hz
    simp only [hcl] at this
    exact this
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hT : Tendsto (fun p : ℕ × ℕ =>
      C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    have h0 : Tendsto (fun p : ℕ × ℕ =>
        C * ∑ w' ∈ S, ‖cls μ (Rw (w' ++ w) (g p.1)) - cls μ (Rw (w' ++ w) (g p.2))‖ ^ 2)
        (atTop ×ˢ atTop) (𝓝 (C * ∑ w' ∈ S, ‖x (w' ++ w) - x (w' ++ w)‖ ^ 2)) := by
      refine Tendsto.const_mul _ (tendsto_finsetSum _ fun w' _ => ?_)
      exact ((((hc _).comp tendsto_fst).sub ((hc _).comp tendsto_snd)).norm).pow 2
    simpa using h0
  have hev := hT.eventually (gt_mem_nhds (pow_pos hε 2))
  rw [prod_atTop_atTop_eq] at hev
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.1 hev
  refine ⟨N, fun k hk l hl z hz => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hbound k l z hz).trans_lt (hN k hk l hl))

end GlobalTheory.CompanionTheory.PresSobA.RwCauchy
end
end

