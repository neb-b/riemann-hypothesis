module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.LiftFlat

theorem flat_of_eval₂Hom_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t).Flat := by
    letI := (MvPolynomial.eval₂Hom i t).toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
    exact Algebra.Smooth.flat (MvPolynomial (Fin d) Λ) D
  have h2 : (MvPolynomial.C : Λ →+* MvPolynomial (Fin d) Λ).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have h3 := RingHom.Flat.comp h2 h1
  rwa [MvPolynomial.eval₂Hom_comp_C] at h3

theorem sub_mem_span_of_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) (J : Ideal D) (μ : D) (g : D →+* D)
    (hJ : ∀ x ∈ J, IsNilpotent x) (hgi : g.comp i = i)
    (hgt : ∀ k, g (t k) - t k ∈ Ideal.span {μ}) (hgJ : ∀ z, g z - z ∈ J) (z : D) :
    g z - z ∈ Ideal.span {μ} := by
  classical
  letI : Algebra (MvPolynomial (Fin d) Λ) D := (MvPolynomial.eval₂Hom i t).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
  let q : D →+* D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mk _
  have hcomm : (q.comp g).comp (MvPolynomial.eval₂Hom i t) = q.comp (MvPolynomial.eval₂Hom i t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply g i, hgi]
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact Ideal.Quotient.eq.mpr (hgt k)
  let φ₁ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mkₐ _ _
  let φ₂ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) :=
    { (q.comp g) with
      commutes' := fun a => by
        change q (g (algebraMap _ D a)) = q (algebraMap _ D a)
        exact RingHom.congr_fun hcomm a }
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra (MvPolynomial (Fin d) Λ) D).FG)
  let I : Ideal (D ⧸ Ideal.span ({μ} : Set D)) :=
    Ideal.span ((fun s => q (g s - s)) '' (S : Set D))
  have hfg : I.FG := Submodule.fg_span (S.finite_toSet.image _)
  have hnil : IsNilpotent I := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg]
    rw [Ideal.span_le]
    rintro _ ⟨s, -, rfl⟩
    exact mem_nilradical.mpr ((hJ _ (hgJ s)).map q)
  have hψ : (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₁ =
      (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₂ := by
    apply AlgHom.ext_of_adjoin_eq_top hS
    intro s hs
    have hmem : q (g s - s) ∈ I := Ideal.subset_span ⟨s, hs, rfl⟩
    rw [map_sub] at hmem
    show Ideal.Quotient.mk I (q s) = Ideal.Quotient.mk I (q (g s))
    exact (Ideal.Quotient.eq.mpr hmem).symm
  have hφ : φ₁ = φ₂ := by
    apply Algebra.FormallyUnramified.ext I hnil
    intro x
    exact congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ x) hψ
  have hz : q z = q (g z) := congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ z) hφ
  exact Ideal.Quotient.eq.mp hz.symm

theorem lift_flat : ∀ {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ} (t : Fin d → D), (MvPolynomial.eval₂Hom i t).Etale → i.Flat ∧ ∀ (J : Ideal D) (μ : D) (g : D →+* D), (∀ x ∈ J, IsNilpotent x) → g.comp i = i → (∀ k, g (t k) - t k ∈ Ideal.span {μ}) → (∀ z, g z - z ∈ J) → ∀ z, g z - z ∈ Ideal.span {μ} := by
  intro Λ D _ _ i d t het
  exact ⟨flat_of_eval₂Hom_etale i t het, fun J μ g hJ hgi hgt hgJ z =>
    sub_mem_span_of_etale i t het J μ g hJ hgi hgt hgJ z⟩

end GlobalTheory.CompanionTheory.LiftFlat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveOfUnramified
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.EtalePerfect

theorem surjective_of_unramified {R S : Type} [CommRing R] [CommRing S] (p : ℕ) (hp : p.Prime)
    (hS : (p : S) = 0) (f : R →+* S) (hu : f.FormallyUnramified) (hft : f.FiniteType)
    (hpow : ∀ x : S, ∃ r, f r = x ^ p) : Function.Surjective f := by
  algebraize [f]
  have hint : Algebra.IsIntegral R S := ⟨fun x => by
    obtain ⟨r, hr⟩ := hpow x
    refine IsIntegral.of_pow hp.pos ?_
    rw [← hr]
    exact isIntegral_algebraMap⟩
  have hfin : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨t, ht2, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R S)
  have hT : (p : S ⊗[R] S) = 0 := by
    rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S), hS, map_zero]
  have hadd : ∀ x y : S ⊗[R] S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hT]
    simp
  have haddS : ∀ x y : S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hS]
    simp
  have hfrob : ∀ u : S ⊗[R] S,
      u ^ p = ((Algebra.TensorProduct.lmul' R (S := S) u) ^ p) ⊗ₜ[R] (1 : S) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [zero_pow hp.ne_zero]
    | tmul a b =>
      obtain ⟨s, hs⟩ := hpow b
      have hs' : b ^ p = s • (1 : S) := by
        rw [← hs, Algebra.smul_def, mul_one]; rfl
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow, hs',
        TensorProduct.tmul_smul, mul_smul_comm, mul_one, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [hadd, hx, hy, map_add (f := _), haddS, TensorProduct.add_tmul]
  have hmul : ∀ u : S ⊗[R] S,
      u * t = (Algebra.TensorProduct.lmul' R (S := S) u ⊗ₜ[R] (1 : S)) * t := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb := ht2 b
      rw [sub_mul, sub_eq_zero] at hb
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b) := by simp
      rw [this, mul_assoc, hb, ← mul_assoc]
      simp
    | add x y hx hy =>
      rw [add_mul, hx, hy, map_add (f := _), TensorProduct.add_tmul, add_mul]
  have hidem : t * t = t := by
    rw [hmul t, ht1]
    exact one_mul t
  have htp : t ^ p = t := (show IsIdempotentElem t from hidem).pow_eq hp.ne_zero
  have ht : t = 1 := by
    rw [← htp, hfrob t, ht1, one_pow]
    rfl
  have hepi : Algebra.IsEpi R S := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro s
    have := ht2 s
    rw [ht, mul_one, sub_eq_zero] at this
    exact this
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

theorem pf_of_etale : ∀ (p : ℕ), p.Prime → ∀ {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E),
    ψ.Etale → D.Pf p P → D.Pf p E := by
  intro p hp P E _ _ ψ hψ hP
  have hEc : (p : E) = 0 := by rw [← map_natCast ψ, hP.char, map_zero]
  have hadd : ∀ {A : Type} [CommRing A], (p : A) = 0 → ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro A _ h x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h]
    simp
  let φ : E →+* E :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hEc }
  let Fp : P →+* P :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hP.char }
  let e : P ≃+* P := RingEquiv.ofBijective Fp hP.bij
  let G : P →+* P := e.symm.toRingHom
  have hFG : ∀ x, (G x) ^ p = x := fun x => e.apply_symm_apply x
  have hGF : ∀ x, G (x ^ p) = x := fun x => e.symm_apply_apply x
  have hcomp : φ.comp (ψ.comp G) = ψ := by
    ext x
    change (ψ (G x)) ^ p = ψ x
    rw [← map_pow, hFG]
  have hUψ : ψ.FormallyUnramified := hψ.formallyUnramified
  have hFTψ : ψ.FiniteType := by
    algebraize [ψ]
    have : Algebra.Etale P E := hψ.toAlgebra
    exact (inferInstance : Algebra.FiniteType P E)
  have hu : φ.FormallyUnramified := by
    rw [← hcomp] at hUψ
    exact RingHom.FormallyUnramified.of_comp hUψ
  have hft : φ.FiniteType := by
    rw [← hcomp] at hFTψ
    exact RingHom.FiniteType.of_comp_finiteType hFTψ
  have hsurj : Function.Surjective φ :=
    surjective_of_unramified p hp hEc φ hu hft (fun x => ⟨x, rfl⟩)
  let N : Ideal E := RingHom.ker φ
  have hN : ∀ x ∈ N, IsNilpotent x := fun x hx => ⟨p, hx⟩
  have hL : EtLift N := _root_.GlobalTheory.CompanionTheory.EtNil.etLift_of_nil N hN
  let eb : (E ⧸ N) ≃+* E := RingHom.quotientKerEquivOfSurjective hsurj
  have heb : ∀ x, eb (Ideal.Quotient.mk N x) = x ^ p := fun x => rfl
  let g : E →+* E ⧸ N := eb.symm.toRingHom
  have hg : ∀ x, g (x ^ p) = Ideal.Quotient.mk N x := by
    intro x
    apply eb.injective
    rw [heb]
    exact eb.apply_symm_apply _
  have hgψ : g.comp ψ = (Ideal.Quotient.mk N).comp (ψ.comp G) := by
    ext x
    apply eb.injective
    change eb (eb.symm (ψ x)) = eb (Ideal.Quotient.mk N (ψ (G x)))
    rw [eb.apply_symm_apply, heb, ← map_pow, hFG]
  obtain ⟨h, ⟨hh1, hh2⟩, -⟩ := hL P E ψ hψ (ψ.comp G) g hgψ
  have hid : h.comp φ = RingHom.id E := by
    refine (hL P E ψ hψ ψ (Ideal.Quotient.mk N) rfl).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · ext x
      change h ((ψ x) ^ p) = ψ x
      rw [← map_pow]
      have := RingHom.congr_fun hh1 (x ^ p)
      simp only [RingHom.comp_apply] at this
      rw [this, hGF]
    · ext x
      have := RingHom.congr_fun hh2 (x ^ p)
      simp only [RingHom.comp_apply] at this
      change Ideal.Quotient.mk N (h (x ^ p)) = _
      rw [this, hg]
    · rfl
    · rfl
  refine ⟨hEc, ?_, ?_⟩
  · intro x y hxy
    have hx := RingHom.congr_fun hid x
    have hy := RingHom.congr_fun hid y
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg h hxy
  · exact hsurj

end GlobalTheory.CompanionTheory.EtalePerfect
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ZetaAlongK

open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem firstCountable_gl : FirstCountableTopology (GL ι 𝔸[k]) := by
  have h1 : SecondCountableTopology (Matrix ι ι 𝔸[k]) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → 𝔸[k]))
  have h2 : SecondCountableTopology (Matrix ι ι 𝔸[k])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι 𝔸[k])).symm.isEmbedding.secondCountableTopology
  have h3 : SecondCountableTopology (GL ι 𝔸[k]) :=
    (Units.isEmbedding_embedProduct (M := Matrix ι ι 𝔸[k])).secondCountableTopology
  exact @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ h3

theorem differentiableAt_globalZeta_of_majorant {F : 𝔸[k] → ℂ} (hFc : Continuous F)
    (χ : HeckeCharacter k) {s₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) {f₀ f₁ f₂ : IdeleGroup k → ℝ}
    (i₀ : Integrable f₀ (ideleMeasure k)) (i₁ : Integrable f₁ (ideleMeasure k))
    (i₂ : Integrable f₂ (ideleMeasure k))
    (b₀ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ s₀.re ≤ f₀ t)
    (b₁ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re - 2 * δ) ≤ f₁ t)
    (b₂ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re + 2 * δ) ≤ f₂ t) :
    DifferentiableAt ℂ (globalZeta F χ) s₀ := by
  have hT : ∀ x : IdeleGroup k, 0 < (IdeleGroup.ideleModule k x : ℝ) :=
    fun x ↦ (IdeleGroup.ideleModule k x).2
  set G : ℂ → IdeleGroup k → ℂ := fun s x ↦
    F x * (χ.toIdele x : ℂ) * ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ^ s with hG
  set G' : ℂ → IdeleGroup k → ℂ :=
    fun s x ↦ G s x * Complex.log (IdeleGroup.ideleModule k x : ℝ) with hG'
  set bound : IdeleGroup k → ℝ := fun x ↦ (f₁ x + f₂ x) / δ with hbound
  have hbound_int : Integrable bound (ideleMeasure k) := (i₁.add i₂).div_const δ
  have hcont' : Continuous (G' s₀) :=
    (continuous_zetaIntegrand hFc χ s₀).mul
      ((Complex.continuous_ofReal.comp continuous_ideleModule_val).clog
        fun x ↦ Complex.ofReal_mem_slitPlane.2 (hT x))
  have hint₀ : Integrable (G s₀) (ideleMeasure k) := by
    refine i₀.mono' (continuous_zetaIntegrand hFc χ s₀).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    simp only [hG]
    rw [norm_zetaIntegrand]
    exact b₀ x
  have hle : ∀ x, ∀ s ∈ Metric.ball s₀ δ, ‖G' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - s₀.re| < δ := by
      have := (Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.1 hs)
      rwa [Complex.sub_re] at this
    have hnorm : ‖G' s x‖ = ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re *
        |Real.log (IdeleGroup.ideleModule k x : ℝ)|) := by
      simp only [hG', hG]
      rw [norm_mul, norm_zetaIntegrand, ← Complex.ofReal_log (hT x).le, Complex.norm_real,
        Real.norm_eq_abs, mul_assoc]
    rw [hnorm]
    calc ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re * |Real.log (IdeleGroup.ideleModule k x : ℝ)|)
        ≤ ‖F x‖ * (((IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (hT x) hδ hre) (norm_nonneg _)
      _ = (‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            ‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ := by ring
      _ ≤ bound x := div_le_div_of_nonneg_right (add_le_add (b₁ x) (b₂ x)) hδ.le
  have hdiff : ∀ x, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s ↦ G s x) (G' s x) s := by
    intro x s _
    have h := ((Complex.hasStrictDerivAt_const_cpow (y := s)
      (Or.inl (Complex.ofReal_ne_zero.2 (hT x).ne'))).hasDerivAt).const_mul
        (F x * (χ.toIdele x : ℂ))
    refine h.congr_deriv ?_
    simp only [hG', hG]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ideleMeasure k) (F := G)
    (F' := G') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s ↦ (continuous_zetaIntegrand hFc χ s).aestronglyMeasurable)
    hint₀ hcont'.aestronglyMeasurable
    (Eventually.of_forall fun x s hs ↦ hle x s hs) hbound_int
    (Eventually.of_forall fun x s hs ↦ hdiff x s hs)
  exact key.2.differentiableAt

def col (m : GL ι 𝔸[k]) (i : ι) : ι → 𝔸[k] := (m : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1

theorem continuous_col (i : ι) : Continuous fun m : GL ι 𝔸[k] => col m i :=
  (Units.continuous_val (M := Matrix ι ι 𝔸[k])).matrix_mulVec continuous_const

theorem continuous_line {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (x : ι → 𝔸[k]) :
    Continuous fun t : 𝔸[k] => Ψ (t • x) :=
  hΨ.comp (continuous_id.smul continuous_const)

def Maj (Ψ : (ι → 𝔸[k]) → ℂ) (i : ι) (C : Set (GL ι 𝔸[k])) : Prop :=
  ∀ a b : ℝ, 1 < a → ∃ f : IdeleGroup k → ℝ, Integrable f (ideleMeasure k) ∧
    ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t

theorem differentiableOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    DifferentiableOn ℂ (fun s => lineZeta Ψ ω s (col m i)) {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set δ := (s₀.re - 1) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨f₀, i₀, b₀⟩ := h s₀.re s₀.re hs₀'
  obtain ⟨f₁, i₁, b₁⟩ := h (s₀.re - 2 * δ) (s₀.re - 2 * δ) (by rw [hδdef]; linarith)
  obtain ⟨f₂, i₂, b₂⟩ := h (s₀.re + 2 * δ) (s₀.re + 2 * δ) (by linarith)
  exact (differentiableAt_globalZeta_of_majorant (F := fun t => Ψ (t • col m i))
    (continuous_line hΨ _) ω hδ i₀ i₁ i₂ (fun t => b₀ _ le_rfl le_rfl m hm t)
    (fun t => b₁ _ le_rfl le_rfl m hm t) (fun t => b₂ _ le_rfl le_rfl m hm t)).differentiableWithinAt

theorem norm_lineZeta_le {Ψ : (ι → 𝔸[k]) → ℂ} (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} {f : IdeleGroup k → ℝ} {a b : ℝ} (hf : Integrable f (ideleMeasure k))
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    ‖lineZeta Ψ ω s (col m i)‖ ≤ ∫ t, f t ∂ideleMeasure k := by
  refine norm_integral_le_of_norm_le hf (Eventually.of_forall fun t => ?_)
  rw [norm_zetaIntegrand (fun a => Ψ (a • col m i)) ω s t]
  exact h _ h1 h2 m hm t

def ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) : ℂ :=
  Ψ ((t : 𝔸[k]) • col y.2 i) * (ω.toIdele t : ℂ) * ((IdeleGroup.ideleModule k t : ℝ) : ℂ) ^ y.1

theorem norm_ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) :
    ‖ig Ψ ω i y t‖ = ‖Ψ ((t : 𝔸[k]) • col y.2 i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ y.1.re :=
  norm_zetaIntegrand (fun a => Ψ (a • col y.2 i)) ω y.1 t

theorem continuous_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (y : ℂ × GL ι 𝔸[k]) : Continuous (ig Ψ ω i y) :=
  continuous_zetaIntegrand (continuous_line hΨ (col y.2 i)) ω y.1

theorem continuous_ig_param {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (t : IdeleGroup k) : Continuous fun y : ℂ × GL ι 𝔸[k] => ig Ψ ω i y t := by
  have c1 : Continuous fun y : ℂ × GL ι 𝔸[k] => Ψ ((t : 𝔸[k]) • col y.2 i) :=
    hΨ.comp ((continuous_const : Continuous fun _ : ℂ × GL ι 𝔸[k] => (t : 𝔸[k])).smul
      ((continuous_col i).comp continuous_snd))
  refine (c1.mul continuous_const).mul ?_
  exact continuous_fst.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k t).2.ne'))

theorem eventually_near {C : Set (GL ι 𝔸[k])} {s₀ : ℂ} {m₀ : GL ι 𝔸[k]} {a b : ℝ} (ha : a < s₀.re)
    (hb : s₀.re < b) : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝[{s | 1 < s.re} ×ˢ C] (s₀, m₀),
      a ≤ y.1.re ∧ y.1.re ≤ b ∧ y.2 ∈ C := by
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] => y.1.re := Complex.continuous_re.comp continuous_fst
  have e1 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), a < y.1.re :=
    hc.continuousAt.eventually (lt_mem_nhds ha)
  have e2 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), y.1.re < b :=
    hc.continuousAt.eventually (gt_mem_nhds hb)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with y y1 y2 y3
  exact ⟨y1.le, y2.le, y3.2⟩

theorem continuousOn_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => ∫ t, ig Ψ ω i y t ∂ideleMeasure k)
      ({s | 1 < s.re} ×ˢ C) := by
  have := firstCountable_gl (k := k) (ι := ι)
  rintro ⟨s₀, m₀⟩ ⟨hs₀, hm₀⟩
  have hs₀' : 1 < s₀.re := hs₀
  obtain ⟨f, hf, hb⟩ := h ((1 + s₀.re) / 2) (s₀.re + 1) (by linarith)
  have hnear := eventually_near (C := C) (m₀ := m₀) (s₀ := s₀) (a := (1 + s₀.re) / 2) (b := s₀.re + 1)
    (by linarith) (by linarith)
  refine continuousWithinAt_of_dominated (bound := f) ?_ ?_ hf ?_
  · exact Eventually.of_forall fun y => (continuous_ig hΨ ω i y).aestronglyMeasurable
  · filter_upwards [hnear] with y hy
    refine Eventually.of_forall fun t => ?_
    rw [norm_ig]
    exact hb _ hy.1 hy.2.1 _ hy.2.2 t
  · exact Eventually.of_forall fun t => (continuous_ig_param hΨ ω i t).continuousWithinAt

theorem continuousOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => lineZeta Ψ ω y.1 (col y.2 i))
      ({s | 1 < s.re} ×ˢ C) :=
  continuousOn_ig hΨ ω h

theorem zt_eq {G : Type} [Group G] (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι)
    (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (g : G) :
    zt π d i Ψ ω s g = lineZeta Ψ ω s (col (kap π d g)⁻¹ i) := rfl

theorem zetaK : EpConv → ZetaK := by
  intro hE G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ
  have hΨc : Continuous Ψ := GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ
  have hcont : Continuous fun g : G => (kap π d g)⁻¹ :=
    ((continuous_const.mul hS.cont).mul continuous_const).inv
  have hC : IsCompact ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) := hK.image hcont
  have hM : Maj Ψ i ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) :=
    fun a b ha => (hE k ι Ψ hΨ).1 i a b _ ha hC
  have hmem : ∀ κ : K, (kap π d κ)⁻¹ ∈ (fun g : G => (kap π d g)⁻¹) '' (K : Set G) :=
    fun κ => ⟨κ, κ.2, rfl⟩
  refine ⟨fun κ => differentiableOn_lineZeta hΨc ω hM (hmem κ), ?_, ?_⟩
  · have hmap : Continuous fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹) :=
      continuous_fst.prodMk (hcont.comp (continuous_subtype_val.comp continuous_snd))
    have hS' : Set.MapsTo (fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹))
        ({s : ℂ | 1 < s.re} ×ˢ Set.univ)
        ({s : ℂ | 1 < s.re} ×ˢ ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))) :=
      fun y hy => ⟨hy.1, hmem y.2⟩
    have h2 := ContinuousOn.comp (continuousOn_lineZeta hΨc ω hM) hmap.continuousOn hS'
    exact h2.congr fun y _ => zt_eq π d i Ψ ω y.1 y.2
  · intro a b ha
    obtain ⟨f, hf, hb⟩ := (hE k ι Ψ hΨ).1 i a b _ ha hC
    exact ⟨∫ t, f t ∂ideleMeasure k, fun s h1 h2 κ => norm_lineZeta_le ω hf hb h1 h2 (hmem κ)⟩

end GlobalTheory.CompanionTheory.ZetaAlongK
end
end

