module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigOfLow
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem integrable_star' {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} {f : Γ → ℂ} (h : Integrable f ν) :
    Integrable (fun g => star (f g)) ν :=
  h.norm.mono' (continuous_star.comp_aestronglyMeasurable h.1) (.of_forall fun g => by simp)

theorem exists_eig_of_low {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (T : A →L[ℂ] A) (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) (w₀ : A) (hw₀ : w₀ ≠ 0) (p : A) (d : ℝ) (hd : 0 < d)
    (h : ∀ a, ‖⟪p, a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re) :
    ∃ (w : A) (c : ℝ), w ≠ 0 ∧ ‖p‖ ^ 2 / (2 * d) ≤ c ∧ T w = (c : ℂ) • w := by
  obtain ⟨s, b, l, -, hTb0, hsum0, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hT'
  have hTb : ∀ i, T (b i) = ((l i : ℝ) : ℂ) • b i := hTb0
  have hsum : ∀ x, HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, x⟫_ℂ) • b i) (T x) := hsum0
  have hone : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have hli : ∀ i, 0 ≤ l i := fun i => by
    have h1 := h (b i)
    rw [hTb, inner_smul_right, hone, mul_one, Complex.ofReal_re] at h1
    exact le_trans (by positivity) h1
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, l i < ‖p‖ ^ 2 / (2 * d) := fun i => by
    by_contra hh
    push_neg at hh
    exact hcon _ _ (b.orthonormal.ne_zero i) hh (hTb i)
  obtain ⟨i0⟩ : Nonempty s := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hw₀ (inner_self_eq_zero.1 ((b.hasSum_inner_mul_inner w₀ w₀).unique hasSum_empty))
  have hC : 0 < ‖p‖ ^ 2 / (2 * d) := (hli i0).trans_lt (hlt i0)
  have key : ∀ i, ⟪p, b i⟫_ℂ * ⟪b i, p⟫_ℂ = ((‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm (b i) p, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key2 : ∀ i, ((l i : ℝ) : ℂ) * ⟪b i, p⟫_ℂ * ⟪p, b i⟫_ℂ = ((l i * ‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [mul_assoc, mul_comm ⟪b i, p⟫_ℂ, key]; push_cast; ring
  have e : (⟪p, p⟫_ℂ).re = ‖p‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) p
  have h1 : HasSum (fun i => ‖⟪p, b i⟫_ℂ‖ ^ 2) (‖p‖ ^ 2) := by
    have h0 := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner p p)
    simp only [Complex.reCLM_apply, key, Complex.ofReal_re, e] at h0
    exact h0
  have h2 : HasSum (fun i => l i * ‖⟪p, b i⟫_ℂ‖ ^ 2) (⟪p, T p⟫_ℂ).re := by
    have h0 := Complex.reCLM.hasSum ((innerSL ℂ p).hasSum (hsum p))
    simp only [innerSL_apply_apply, inner_smul_right, Complex.reCLM_apply, key2, Complex.ofReal_re] at h0
    exact h0
  have h3 : (⟪p, T p⟫_ℂ).re ≤ ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 :=
    hasSum_le (fun i => mul_le_mul_of_nonneg_right (hlt i).le (by positivity)) h2 (h1.mul_left (‖p‖ ^ 2 / (2 * d)))
  have h5 := h p
  have e2 : ‖⟪p, p⟫_ℂ‖ = ‖p‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e2] at h5
  have hP : 0 < ‖p‖ ^ 2 := by
    by_contra hh
    have : ‖p‖ ^ 2 = 0 := le_antisymm (not_lt.1 hh) (by positivity)
    rw [this] at hC
    simp at hC
  have e3 : ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 = (‖p‖ ^ 2) ^ 2 / d / 2 := by field_simp
  have h6 : 0 < (‖p‖ ^ 2) ^ 2 / d := by positivity
  linarith

theorem eigA : EigA := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd w₀ hw₀ hc0 i hi v hm0
  have hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν := integrable_star' hm0
  have hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν := integrable_star' hc0
  have hne : w₀ ≠ 0 := fun h => by simp [h] at hw₀
  have hdense : (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro u hu
    refine PositivityTheory.UnitaryDecomposition.X4.eq_zero_of_orth hd hne fun g => ?_
    have hg : σ g w₀ ∈ Submodule.span ℂ (Set.range fun x => σ x w₀) := Submodule.subset_span ⟨g, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal hg hu
  have hlow := _root_.GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef σ ρ d hd.1 hσ hρ w₀ v i hi.1 hdense
    (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) (coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc)
    (_root_.GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate ν σ ρ hσ hρ w₀ v hc hm) (_root_.GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge ν σ ρ d hσ hρ hd w₀ hw₀ hc i hi)
  have hlow' : ∀ a, ‖⟪ContinuousLinearMap.adjoint i v, a⟫_ℂ‖ ^ 2 / d ≤
      (⟪a, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm a⟫_ℂ).re := fun a => by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hlow a
  obtain ⟨w, c, hw, hcb, hTw⟩ := exists_eig_of_low _ (GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator
    (_root_.GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp ν σ ρ d hσ hρ hd v hm)) (_root_.GlobalTheory.CompanionTheory.RgHeA.isSelfAdjoint_coefOp ν σ ρ hσ hρ v hm) w₀ hne _ d hd.1 hlow'
  refine ⟨w, c, hw, hcb, fun b => ⟨integrable_mul_inner hσ hm b w, ?_⟩⟩
  rw [← inner_coefOp ν σ hσ _ hm, hTw, inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem eq_zero_of_pow_mul {R : Type} [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤) (b : R)
    (h : ∀ a ∈ s, ∃ n : ℕ, a ^ n * b = 0) : b = 0 := by
  let K : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R b)
  have hK : K.radical = ⊤ := by
    rw [eq_top_iff, ← hs, Ideal.span_le]
    intro a ha
    obtain ⟨n, hn⟩ := h a ha
    exact ⟨n, by simpa [K, LinearMap.mem_ker] using hn⟩
  have h1 : (1 : R) ∈ K := by
    rw [Ideal.radical_eq_top.1 hK]; trivial
  simpa [K, LinearMap.mem_ker] using h1

theorem exists_pow_mul_of_away {R : Type} [CommRing R] (a x : R)
    (h : algebraMap R (Localization.Away a) x = 0) : ∃ n : ℕ, a ^ n * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) x).1 h
  exact ⟨n, hm⟩

theorem isUnit_away {R : Type} [CommRing R] (a : R) : IsUnit (algebraMap R (Localization.Away a) a) :=
  IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a

theorem exists_ideal_of_local {R : Type} [CommRing R] (Q : ∀ (R' : Type) [CommRing R'], (R →+* R') → Prop)
    (stab : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (g : R →+* R') (h : R' →+* R''), Q R' g → Q R'' (h.comp g))
    (loc : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (s : Set R'), Ideal.span s = ⊤ →
      (∀ a ∈ s, Q (Localization.Away a) ((algebraMap R' _).comp g)) → Q R' g)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤) (I : R → Ideal R)
    (hI : ∀ f ∈ s, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g f) → (Q R' g ↔ I f ≤ RingHom.ker g)) :
    ∃ J : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Q R' g ↔ J ≤ RingHom.ker g := by
  classical
  let B : R → Type := fun f => Localization.Away (Ideal.Quotient.mk (I f) f)
  let b : ∀ f, R →+* B f := fun f => (algebraMap (R ⧸ I f) (B f)).comp (Ideal.Quotient.mk (I f))
  have bu : ∀ f, IsUnit (b f f) := fun f => isUnit_away _
  have bI : ∀ f, I f ≤ RingHom.ker (b f) := fun f x hx => by
    simp [b, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have bQ : ∀ f ∈ s, Q (B f) (b f) := fun f hf => (hI f hf _ _ (bu f)).2 (bI f)

  have fac : ∀ f ∈ s, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Q R' g → IsUnit (g f) →
      ∃ h : B f →+* R', h.comp (b f) = g := fun f hf R' _ g hq hu => by
    have hle := (hI f hf R' g hu).1 hq
    let g₁ : R ⧸ I f →+* R' := Ideal.Quotient.lift (I f) g fun x hx => hle hx
    have hu' : IsUnit (g₁ (Ideal.Quotient.mk (I f) f)) := by
      rw [show g₁ (Ideal.Quotient.mk (I f) f) = g f from Ideal.Quotient.lift_mk _ _ _]; exact hu
    refine ⟨IsLocalization.Away.lift (S := B f) (Ideal.Quotient.mk (I f) f) hu', ?_⟩
    ext x
    change IsLocalization.Away.lift (S := B f) (Ideal.Quotient.mk (I f) f) hu' (algebraMap (R ⧸ I f) (B f) (Ideal.Quotient.mk (I f) x)) = g x
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.lift_mk _ _ _

  refine ⟨⨅ f ∈ s, RingHom.ker (b f), fun R' _ g => ⟨fun hq a ha => ?_, fun hJ => ?_⟩⟩
  · have ha' : ∀ f ∈ s, b f a = 0 := fun f hf => by
      have := (Submodule.mem_iInf _).1 ha f
      exact (Submodule.mem_iInf _).1 this hf
    refine eq_zero_of_pow_mul (g '' (s : Set R)) ?_ (g a) ?_
    · rw [← Ideal.map_span, hs, Ideal.map_top]
    · rintro _ ⟨f, hf, rfl⟩
      let L := Localization.Away (g f)
      obtain ⟨h, hh⟩ := fac f hf L ((algebraMap R' L).comp g) (stab _ _ _ _ hq)
        (isUnit_away _)
      apply exists_pow_mul_of_away
      have := congrArg (fun q => q a) hh
      simpa [ha' f hf] using this.symm
  · set J : Ideal R := ⨅ f ∈ s, RingHom.ker (b f) with hJdef
    suffices H : Q (R ⧸ J) (Ideal.Quotient.mk J) by
      have := stab _ _ _ (Ideal.Quotient.lift J g fun x hx => hJ hx) H
      have e : (Ideal.Quotient.lift J g fun x hx => hJ hx).comp (Ideal.Quotient.mk J) = g := by
        exact RingHom.ext fun x => Ideal.Quotient.lift_mk J g fun x hx => hJ hx
      rwa [e] at this
    refine loc _ _ (Ideal.Quotient.mk J '' (s : Set R)) (by rw [← Ideal.map_span, hs]; exact Ideal.map_top _) ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (hI f hf _ ((algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f))).comp (Ideal.Quotient.mk J))
      (isUnit_away (Ideal.Quotient.mk J f))).2 fun x hx => ?_
    have key : ∀ f' ∈ s, ∃ n : ℕ, b f' f ^ n * b f' x = 0 := fun f' hf' => by
      let L := Localization.Away (b f' f)
      have h1 := (hI f hf L ((algebraMap (B f') L).comp (b f')) (isUnit_away _)).1
        (stab _ _ _ _ (bQ f' hf'))
      exact exists_pow_mul_of_away _ _ (h1 hx)
    choose! n hn using key
    have hmem : Ideal.Quotient.mk J f ^ (s.sup n) * Ideal.Quotient.mk J x = 0 := by
      rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      refine (Submodule.mem_iInf _).2 fun f' => (Submodule.mem_iInf _).2 fun hf' => ?_
      have hle : n f' ≤ s.sup n := Finset.le_sup hf'
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [RingHom.mem_ker, map_mul, map_pow, hd, pow_add, mul_comm (b f' f ^ n f'), _root_.mul_assoc, hn f' hf', mul_zero]
    have hu : IsUnit (algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f)) (Ideal.Quotient.mk J f ^ (s.sup n))) := by
      rw [map_pow]; exact (isUnit_away _).pow _
    have := congrArg (algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f))) hmem
    rw [map_mul, map_zero] at this
    exact (hu.mul_right_eq_zero).1 this

end GlobalTheory.CompanionTheory.TrivLoc

namespace GlobalTheory.CompanionTheory.TrivLoc

variable {S : Scheme.{0}} {A Y : Over S}

def IsTrivAt (N : LB (A ⊗ Y).left) {T : Over S} (y : T ⟶ Y) : Prop :=
  Triv (ev N (fst A T) (snd A T ≫ y))

theorem IsTrivAt.comp {N : LB (A ⊗ Y).left} {T T' : Over S} {y : T ⟶ Y} (h : IsTrivAt N y) (u : T' ⟶ T) :
    IsTrivAt N (u ≫ y) := by
  have e : lift (fst A T') (snd A T' ≫ u ≫ y) = lift (fst A T') (snd A T' ≫ u) ≫ lift (fst A T) (snd A T ≫ y) := by
    ext <;> simp
  unfold IsTrivAt ev at *
  rw [e, Over.comp_left]
  exact GlobalTheory.Biadditive.triv_pull_comp h _

def Locus (N : LB (A ⊗ Y).left) {T : Scheme.{0}} (t : T ⟶ Y.left) : Prop :=
  IsTrivAt N (Over.homMk t rfl : Over.mk (t ≫ Y.hom) ⟶ Y)

theorem locus_left_iff {N : LB (A ⊗ Y).left} {T : Over S} (y : T ⟶ Y) : Locus N y.left ↔ IsTrivAt N y := by
  have w : y.left ≫ Y.hom = T.hom := Over.w y
  let u : T ⟶ Over.mk (y.left ≫ Y.hom) := Over.homMk (𝟙 _) (by simp [w])
  let v : Over.mk (y.left ≫ Y.hom) ⟶ T := Over.homMk (𝟙 _) (by simp [w])
  constructor
  · intro h
    have := IsTrivAt.comp h u
    have e : u ≫ (Over.homMk y.left rfl : Over.mk (y.left ≫ Y.hom) ⟶ Y) = y := by
      ext; simp [u]
    rwa [e] at this
  · intro h
    have := IsTrivAt.comp h v
    have e : v ≫ y = (Over.homMk y.left rfl : Over.mk (y.left ≫ Y.hom) ⟶ Y) := by
      ext; simp [v]
    unfold Locus
    rwa [e] at this

theorem Locus.comp {N : LB (A ⊗ Y).left} {T T' : Scheme.{0}} {t : T ⟶ Y.left} (h : Locus N t) (u : T' ⟶ T) :
    Locus N (u ≫ t) := by
  let v : Over.mk ((u ≫ t) ≫ Y.hom) ⟶ Over.mk (t ≫ Y.hom) := Over.homMk u (by simp)
  have := IsTrivAt.comp h v
  have e : v ≫ (Over.homMk t rfl : Over.mk (t ≫ Y.hom) ⟶ Y) = (Over.homMk (u ≫ t) rfl : Over.mk ((u ≫ t) ≫ Y.hom) ⟶ Y) := by
    ext; simp [v]
  unfold Locus
  rwa [e] at this

end GlobalTheory.CompanionTheory.TrivLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemKLOfTrivLam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KLFinite

theorem memKL_of_triv_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (x : T ⟶ A) (hx : Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A))) : GlobalTheory.MemKL A L x := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hl : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e := (triv_ev_iff hP _ _).1 hx
    rwa [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd] at e
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hl, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

theorem memKL_congr {S X : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {t t' : X ⟶ S} (e : t = t')
    (x : Over.mk t ⟶ A) (x' : Over.mk t' ⟶ A) (hl : x.left = x'.left) (h : GlobalTheory.MemKL A L x) :
    GlobalTheory.MemKL A L x' := by
  subst e
  have e : x = x' := Over.OverMorphism.ext hl
  rwa [← e]

theorem finite_memKL (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B)
    (M : LB B.left) (hM : M.IsLB) (hA : Out.RelAmple B M) :
    Finite {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x} := by
  obtain ⟨H, j, -, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have : IsFinite H.hom := hfin
  have : IsFinite (toUnit H).left := hfin
  have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
  refine Finite.of_surjective
    (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} ↦
      (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x})) fun x ↦ ?_
  obtain ⟨z, hz⟩ := (hH _ _).1 x.2
  exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩

theorem kFinite : KFinite := by
  intro S A _ hA L hL hamp k _ _ t
  let B : Over (Sp k) := (Over.pullback t).obj A
  have gp : IsGrpPullback B A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme B := by
    have := hA.comm
    have hc : IsCommMonObj B := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← gp.2 T x y (pushPt gp.1.w x) (pushPt gp.1.w y) rfl rfl,
        ← gp.2 T y x (pushPt gp.1.w y) (pushPt gp.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) gp.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) gp.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) gp.1 hA.geomConnected⟩
  have := hA.proper
  have hM : (L.pull (pullback.fst A.hom t)).IsLB := pull_isLB hL _
  have hAmp : Out.RelAmple B (L.pull (pullback.fst A.hom t)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp (IsPullback.of_hasPullback A.hom t)
  have hK := finite_memKL k B hB _ hM hAmp
  have hw : ∀ x : Over.mk t ⟶ A, x.left ≫ A.hom = 𝟙 (Sp k) ≫ t := fun x ↦ by
    rw [Over.w x, Category.id_comp]; rfl
  let pt : (Over.mk t ⟶ A) → (𝟙_ (Over (Sp k)) ⟶ B) := fun x ↦ GlobalTheory.AbDual.liftPt gp (𝟙 _) x.left (hw x)
  have hpt : ∀ x, (pt x).left ≫ pullback.fst A.hom t = x.left := fun x ↦
    GlobalTheory.AbDual.liftPt_left gp _ _ _
  have hmem : ∀ x : Over.mk t ⟶ A, Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A)) →
      GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) (pt x) := fun x hx ↦
    GlobalTheory.memKL_of_push gp hL hM ((cls_eq_iff hM hM).1 rfl) (pt x)
      (memKL_congr (Category.id_comp t).symm x _ (hpt x).symm (memKL_of_triv_lam hL x hx))
  have : Finite {x : Over.mk t ⟶ A | Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A))} :=
    Finite.of_injective
      (fun x ↦ (⟨pt x.1, hmem x.1 x.2⟩ : {y : 𝟙_ (Over (Sp k)) ⟶ B //
        GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) y})) fun x y e ↦ by
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      have e' : pt x.1 = pt y.1 := congrArg Subtype.val e
      rw [← hpt x.1, ← hpt y.1, e']
  exact Set.toFinite _

end GlobalTheory.CompanionTheory.KLFinite
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_base_change : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}} (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀), IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) → ∀ (M₀ : LB Y₀), M₀.IsLB → Perf f₀ M₀ → Nonempty (Perf f (M₀.pull π)) := by
  first | exact @GlobalTheory.CompanionTheory.PerfBase.perf_pull | exact GlobalTheory.CompanionTheory.PerfBase.perf_pull | (intros; apply GlobalTheory.CompanionTheory.PerfBase.perf_pull <;> assumption)
end

