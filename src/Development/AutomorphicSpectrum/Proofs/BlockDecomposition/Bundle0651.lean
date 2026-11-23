module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
section
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisTop

theorem ext_mul_eq {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ)
    (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q) (hK : ∀ p ∈ P, p ∈ K → f p = 0)
    {p k : G} (hp : p ∈ P) (hk : k ∈ K) : ext K P f (p * k) = f p := by
  unfold ext
  have h : ∃ k' : K, p * k * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [dite_eq_left h]
  have h1 := h.choose_spec
  have hm : k * (h.choose : G)⁻¹ ∈ P := by
    have := P.mul_mem (P.inv_mem hp) h1
    simpa [mul_assoc] using this
  have hmK : k * (h.choose : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem h.choose.2)
  rw [mul_assoc, hadd p hp _ hm, hK _ hm hmK, add_zero]

theorem absA_pos' {D : D7} (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr fun h0 => by simp [h0] at h

section Gen

variable {E R : Type} [Field E] [CommRing R] (A : Ad E R) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set ι)

theorem uH_mul (hmul : ∀ p ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))), ∀ q ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))),
      bdet ((Sum.inl '' S : Set (ι ⊕ ι))) (p * q) = bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p * bdet ((Sum.inl '' S : Set (ι ⊕ ι))) q)
    (hlg : ∀ x y, A.lg (x * y) = A.lg x + A.lg y)
    (hk0 : ∀ p ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))), p ∈ A.kGL (ι ⊕ ι) → A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p) = 0)
    {p k : A.U ε ι} (hp : p ∈ A.uQ ε S) (hk : k ∈ A.uK ε ι) :
    A.uH ε S (p * k) = A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p.1) :=
  ext_mul_eq (A.uK ε ι) (A.uQ ε S) (fun p => A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p.1))
    (fun p hp q hq => by
      show A.lg (bdet _ (p.1 * q.1)) = _
      exact (congrArg A.lg (hmul p.1 hp q.1 hq)).trans (hlg _ _))
    (fun p hp hk => hk0 _ hp hk) hp hk

end Gen

theorem exp_uH_eq (hDict : Dict) (hBd : BdetLaw) {D : D7} {χ : (AE D)ˣ →* Circle} {n : ℕ}
    (hGood : (adCM D.sp.cm.sig χ).Good) (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n)
    (hP : ∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n)))
    (hK : ∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin n))
    (hdet : ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Ψ g).1 = Matrix.GeneralLinearGroup.det a)
    (hI : Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin n)))
    {H : GlobalTheory.StdUnn.G D n → ℝ≥0} (hH : GlobalTheory.StdUnn.IsHeight H) (x : GlobalTheory.StdUnn.G D n) :
    Real.exp ((adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) = (H x : ℝ) := by
  have hBd' := hBd _ _ (adCM D.sp.cm.sig χ) hGood.toGoodL (Fin n ⊕ Fin n) (Sum.inl '' Set.univ)
  obtain ⟨p, hp, k, hk, e⟩ := hI (Ψ x)
  have h1 := uH_mul (adCM D.sp.cm.sig χ) (-1) (Set.univ : Set (Fin n)) hBd'.2.1 hGood.lgmul hBd'.2.2.2.2.1 hp hk
  rw [← e] at h1
  have hp₀ : Ψ.symm p ∈ GlobalTheory.StdUnn.P D n := (hP _).2 (by simpa using hp)
  have hk₀ : Ψ.symm k ∈ GlobalTheory.StdUnn.K D n := (hK _).2 (by simpa using hk)
  have hx : x = Ψ.symm p * Ψ.symm k := by rw [← map_mul, ← e, ContinuousMulEquiv.symm_apply_apply]
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp₀
  have h2 := hdet _ a ha
  rw [ContinuousMulEquiv.apply_symm_apply] at h2
  have h3 := hH _ hp₀ a ha _ hk₀
  rw [← hx] at h3
  have h4 : (adCM D.sp.cm.sig χ).lg (Matrix.GeneralLinearGroup.det a) =
      Real.log (absA D (Matrix.GeneralLinearGroup.det a)) := by
    have e5 := (hDict D.host.F D.host.E).2.2.2.2 (Matrix.GeneralLinearGroup.det a)
    show Real.log _ = _
    rw [e5]
  rw [h1, h2, h4, h3, Real.exp_log (by exact_mod_cast absA_pos' _)]

theorem law_div {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {G' : Type} [Group G'] [TopologicalSpace G']
    (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* G') (P' : Subgroup G') (η : G' → ℝ) (c : G' → ℂ)
    (hP : ∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ P') (hleft : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g)
    (hc : ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      c (Ψ g) = χ (Matrix.GeneralLinearGroup.det a))
    {H : GlobalTheory.StdUnn.G D n → ℝ≥0} (hH : GlobalTheory.StdUnn.IsHeight H) (hexp : ∀ x, Real.exp (η (Ψ x)) = (H x : ℝ))
    {s₁ : ℂ} {φ : GlobalTheory.StdUnn.G D n → ℂ} (hφ : GlobalTheory.StdUnn.IsSection χ s₁ φ) :
    ∀ q ∈ GlobalTheory.StdUnn.P D n, ∀ g, φ (q * g) * Complex.exp (-(s₁ + (n : ℂ) / 2) * η (Ψ (q * g))) =
      c (Ψ q) * (φ g * Complex.exp (-(s₁ + (n : ℂ) / 2) * η (Ψ g))) := by
  intro q hq g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
  have hq' := (hP q).1 hq
  have h3 : η (Ψ q) = Real.log (absA D (Matrix.GeneralLinearGroup.det a)) := by
    have h := hH q hq a ha 1 (one_mem _)
    rw [mul_one] at h
    rw [← Real.log_exp (η (Ψ q)), hexp q, h]
  rw [hφ.1 q hq a ha g, map_mul, hleft _ hq' _, h3, hc q a ha, npow_eq_exp (absA_pos' _)]
  have key : Complex.exp (((Real.log (absA D (Matrix.GeneralLinearGroup.det a)) : ℝ) : ℂ) * (s₁ + (n : ℂ) / 2)) *
      Complex.exp (-(s₁ + (n : ℂ) / 2) * ((Real.log (absA D (Matrix.GeneralLinearGroup.det a)) + η (Ψ g) : ℝ) : ℂ)) =
      Complex.exp (-(s₁ + (n : ℂ) / 2) * (η (Ψ g) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * φ g) * key

theorem fin_div {D : D7} {n : ℕ} {G' : Type} [Group G'] [TopologicalSpace G']
    (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* G') (K' : Subgroup G') (η : G' → ℝ)
    (hK : ∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ K') (hright : ∀ g, ∀ k ∈ K', η (g * k) = η g)
    {φ : GlobalTheory.StdUnn.G D n → ℂ} (hφ : IsKFinite (GlobalTheory.StdUnn.K D n) φ) (t : ℂ) (f : GlobalTheory.StdUnn.G D n → ℂ)
    (hf : ∀ x, f x = φ x * Complex.exp (t * η (Ψ x))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Ψ.symm k))) := by
  haveI : FiniteDimensional ℂ (kSpan (GlobalTheory.StdUnn.K D n) φ) := hφ
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
    _ ≤ (kSpan (GlobalTheory.StdUnn.K D n) φ).map (LinearMap.mulRight ℂ (fun x => Complex.exp (t * η (Ψ x)))))
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => φ (x * Ψ.symm k), Submodule.subset_span ⟨Ψ.symm k, (hK _).2 (by simpa using k.2), rfl⟩, ?_⟩
  funext x
  simp [hf, LinearMap.mulRight_apply, map_mul, hright _ _ k.2]

theorem fun_eq {X : Type} (η : X → ℝ) (H : X → ℝ≥0) (hexp : ∀ x, Real.exp (η x) = (H x : ℝ)) (φ : X → ℂ)
    (s₁ z c : ℂ) : (fun x => Complex.exp ((z + c) * η x) * (φ x * Complex.exp (-(s₁ + c) * η x))) =
      fun x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x := by
  funext x
  have hpos : (0 : ℝ) < H x := by rw [← hexp x]; exact Real.exp_pos _
  have hlog : Real.log (H x) = η x := by rw [← hexp x, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, hlog]
  have key : Complex.exp ((z + c) * η x) * Complex.exp (-(s₁ + c) * η x) = Complex.exp (η x * (z - s₁)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination φ x * key

theorem assemble {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G'] (hFar : Far) (hGlue : Glue) (Φ : G ≃ₜ* G')
    (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ) (R0 : ℝ) (hK : IsCompact (K' : Set G'))
    (hPar : IsPar Γ' K' P' c) (hHt : IsHt Γ' K' P' η) (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P')
    (hconv : ∀ x : ℝ, R0 < x → Conv Γ' P' fun g => x * η g) (f : G → ℂ) (hf : Continuous f)
    (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) (A : ℂ → ℂ) (Hh : ℂ → G → ℂ) (R1 : ℝ) (hA : Differentiable ℂ A)
    (hAne : ∃ z, A z ≠ 0) (hHd : ∀ g, Differentiable ℂ (Hh · g)) (hHc : Continuous fun y : ℂ × G => Hh y.1 y.2)
    (hHeq : ∀ z : ℂ, R1 < z.re → ∀ g, Hh z g = A z * GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g)
    (w : ℝ) (F : ℂ → G → ℂ) (hF : ∀ z : ℂ, (fun x => Complex.exp ((z + (w : ℂ)) * η (Φ x)) * f x) = F z) (s₀ : ℂ) :
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
      (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
      ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets P Γ → ℝ, Summable u ∧
          ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term P Γ (F z) g q‖ ≤ u q) ∧
        ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum P Γ (F z) g := by
  obtain ⟨R, hR1, hR0⟩ : ∃ R : ℝ, R1 ≤ R ∧ R0 ≤ R := ⟨max R1 R0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨hmaj, hdiff, hcont, hinv⟩ := hFar G G' Φ Γ P Γ' K' P' c η R hK hPar hHt hΓ hP
    (fun x hx => hconv x (lt_of_le_of_lt hR0 hx)) f hf hlaw
  obtain ⟨U', d', E', hU'o, hU'r, hs₀', hd', hE'd, hE'c, hE'i, hE'eq⟩ :=
    hGlue G Γ (fun i x => (i : G) * x)
      (fun z g => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) Hh A R hA hAne hHd hHc
      (fun z hz x => hHeq z (lt_of_le_of_lt hR1 hz) x) hdiff hcont
      (fun z i x => hinv z i i.2 x) (s₀ + (w : ℂ))
  refine ⟨(· + (w : ℂ)) ⁻¹' U', Polynomial.taylor (w : ℂ) d', fun z g => E' (z + (w : ℂ)) g,
    R - w, hU'o.preimage (continuous_id.add continuous_const), hU'r.preimage_add _, hs₀', ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hd' ((Polynomial.taylor_eq_zero _ d').1 h)
  · intro g
    exact (hE'd g).comp (differentiableOn_id.add_const _) (fun z hz => hz)
  · refine hE'c.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn ?_
    intro y hy
    exact ⟨hy.1, Set.mem_univ _⟩
  · intro z hz γ hγ g
    exact hE'i (z + (w : ℂ)) hz ⟨γ, hγ⟩ g
  · intro z hz
    have hz' : R < (z + (w : ℂ)).re := by
      have : (z + (w : ℂ)).re = z.re + w := by simp
      rw [this]; linarith
    refine ⟨fun C hC => ?_, fun g => ?_⟩
    · obtain ⟨u, hu, hb⟩ := hmaj (z + (w : ℂ)) hz' C hC
      refine ⟨u, hu, fun g hg q => ?_⟩
      rw [← hF z]
      exact hb g hg q
    · show E' (z + (w : ℂ)) g = _
      rw [hE'eq (z + (w : ℂ)) hz' g, Polynomial.taylor_eval, hF z]

theorem eTop : ETop := by
  intro hDict hDI hCM hGT hBd hExt hPar hSg hStd hIwa hScal hFar hGlue
  intro D n hn χ b hχ hres H hH s₁ φ hφ s₀
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hur := GlobalTheory.HeckeAdjoint.unramified_host D
  have hpow := GlobalTheory.LFun.resEtaPow_of_resEta _ _ hcm.2.2.1 χ b ((GlobalTheory.LFun.resEta_iff χ b).1 hres)
  have hGood : (adCM D.sp.cm.sig χ).Good := hCM _ _ D.sp.cm.sig χ b hcm hur hχ hpow
  obtain ⟨_, _, _, hT2, hLC, _, hKc⟩ := hGT _ _ (adCM D.sp.cm.sig χ) hGood (Fin n) (-1)
  obtain ⟨Ψ, hΓ, hP, hK, hdet⟩ := hStd hDict hDI D χ n
  have hI := hIwa D χ n
  obtain ⟨hPar1, hHt1, -⟩ := (hPar _ _ (adCM D.sp.cm.sig χ) hGood (Fin n) (-1) Set.univ).2 (by rw [inf_idem]; exact hI)
  rw [inf_idem] at hPar1
  have hW := hSg _ _ D.sp.cm.sig χ b hcm hur hχ hpow (-1) (Fin n) (by simp; omega) hI
  have hexp : ∀ x, Real.exp ((adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) = (H x : ℝ) :=
    fun x => exp_uH_eq hDict hBd hGood Ψ hP hK hdet hI hH x
  obtain ⟨R0, D0, Op0, H0, hwall⟩ := hW ℂ (1 : (adCM D.sp.cm.sig χ).uK (-1) (Fin n) →* (ℂ →L[ℂ] ℂ)) continuous_const
  have hf : Continuous fun x => φ x * Complex.exp (-(s₁ + (n : ℂ) / 2) * (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) :=
    hφ.2.1.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (hHt1.cont.comp Ψ.continuous))))
  have hlaw := law_div Ψ _ _ ((adCM D.sp.cm.sig χ).uC (-1) (Fin n)) hP hHt1.left (fun g a ha => congrArg (fun u => ((χ u : Circle) : ℂ)) (hdet g a ha))
    hH hexp hφ
  have hfin := fin_div Ψ _ _ hK hHt1.right hφ.2.2 (-(s₁ + (n : ℂ) / 2))
    (fun x => φ x * Complex.exp (-(s₁ + (n : ℂ) / 2) * (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x))) (fun x => rfl)
  obtain ⟨A0, Hh, R1, hA0, hA0ne, hHd, hHc, hHeq, -⟩ :=
    hScal _ _ Ψ _ _ _ _ _ _ _ _ hKc hPar1 hHt1 hΓ hP hW _ hf hlaw hfin
  exact assemble hFar hGlue Ψ _ _ _ _ _ _ _ R0 hKc hPar1 hHt1 hΓ hP hwall.convR _ hf hlaw A0 Hh R1 hA0 hA0ne hHd hHc hHeq
    ((n : ℝ) / 2) (fun z x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x)
    (fun z => by
      have e := fun_eq (fun x => (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) H hexp φ s₁ z ((n : ℂ) / 2)
      push_cast
      exact e) s₀

end GlobalTheory.CompanionTheory.SwEisTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishing
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisZero

open GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks (pairing gramQ mmul)

variable {D : D7} {m : ℕ}

theorem heis_zy (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {n : ℕ} (y : Mx D V.rank n) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : EC.Heisenberg₂ ψ V (zy y) Φ z = pairing V.gram ψ z y * Φ z := by
  have hx : xPart (zy y) = 0 := by
    ext i j
    simp only [xPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Matrix.zero_apply]
  have hy : yPart (zy y) = y := by
    ext i j
    simp only [yPart, zy, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  have hin : ∀ x : Mx D V.rank n, GlobalTheory.StdUnn.inner V x y = gramQ V.gram x y := fun x => by
    unfold GlobalTheory.StdUnn.inner gramQ mmul
    rw [Matrix.mul_assoc]
    rfl
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner]
  unfold EC.Heisenberg₂
  have htr0 : GlobalTheory.StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [hx, hy, h0, add_zero, Matrix.trace_zero, halfTr, htr0, mul_zero, add_zero, hin]
  rfl

theorem pairing_add_right (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (x y y' : Mx D m n) : pairing T ψ x (y + y') = pairing T ψ x y * pairing T ψ x y' := by
  unfold pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA gramQ mmul
  rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]

theorem continuous_pairing (T : Matrix (Fin m) (Fin m) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {n : ℕ} (x : Mx D m n) : Continuous (pairing T ψ x) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold pairing gramQ mmul
  exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)

theorem pairing_zero_left (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ}
    (y : Mx D m n) : pairing T ψ 0 y = 1 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj (0 : Mx D m n) = 0 := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.adj, Formalism.UG.cT]
  simp [pairing, gramQ, mmul, h, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA]


open Classical in
theorem char_integral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {n : ℕ}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    ∫ y in 𝓕, pairing V.gram ψ (ξ.map (incA D)) y ∂μ = if ξ = 0 then 1 else 0 := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.GramAnnih.ratMx_annihilator D V.rank n V.gram (isHermND_gram V) ψ hψ
  split_ifs with hξ
  · subst hξ
    have h0 : (0 : Matrix (Fin V.rank) (Fin n) D.host.E).map (incA D) = 0 := by
      ext i j
      simp
    simp only [h0, pairing_zero_left, setIntegral_const, smul_eq_mul, mul_one]
    simp [Measure.real, hμ.2.2]
  · set ξ' : Mx D V.rank n := ξ.map (incA D) with hξ'
    have hrat : ξ' ∈ ratMx D V.rank n := ⟨ξ, rfl⟩
    have hne : ξ' ≠ 0 := by
      intro h
      apply hξ
      exact Matrix.ext fun i j => incA_injective ((congrFun (congrFun h i) j).trans (map_zero (incA D)).symm)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, pairing V.gram ψ ξ' y₀ ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (h2 ξ' hrat hc)
    have hper : ∀ γ ∈ ratMx D V.rank n, ∀ a, pairing V.gram ψ ξ' (γ + a) = pairing V.gram ψ ξ' a := by
      intro γ hγ a
      rw [pairing_add_right, (h1 γ).2 hγ ξ' hrat, one_mul]
    have key := GlobalTheory.TowerRestrict.setIntegral_add_right hμ (pairing V.gram ψ ξ') hper y₀
    simp only [pairing_add_right, integral_mul_const] at key
    have : (∫ y in 𝓕, pairing V.gram ψ ξ' y ∂μ) * (pairing V.gram ψ ξ' y₀ - 1) = 0 := by
      rw [mul_sub, mul_one, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hy₀)


open Classical in
theorem zero : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  intro D ψ hψ θ hθ V n μ 𝓕 hμ Φ hΦ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI i6 : DiscreteTopology (ratMx D V.rank n) := i5
  haveI i7 : SecondCountableTopology (ratMx D V.rank n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D V.rank n) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) := by
    let g : Matrix (Fin V.rank) (Fin n) D.host.E → ratMx D V.rank n := fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩
    have hg : Function.Injective g := by
      intro a b h
      have h' := congrArg Subtype.val h
      exact Matrix.ext fun i j => incA_injective (congrFun (congrFun h' i) j)
    exact hg.countable
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; exact ENNReal.one_ne_top)
  simp only [heis_zy]
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → Mx D V.rank n → ℂ :=
    fun ξ y => pairing V.gram ψ (ξ.map (incA D)) y * Φ (ξ.map (incA D)) with hF
  have hnorm : ∀ ξ y, ‖F ξ y‖ = ‖Φ (ξ.map (incA D))‖ := by
    intro ξ y
    simp only [hF, norm_mul, pairing, hψ.2.1, one_mul]
  have hint : ∀ ξ, Integrable (F ξ) (μ.restrict 𝓕) := fun ξ =>
    (integrable_const ‖Φ (ξ.map (incA D))‖).mono'
      ((continuous_pairing V.gram hψ _).mul continuous_const).aestronglyMeasurable
      (ae_of_all _ fun y => (hnorm ξ y).le)
  have hsum : Summable fun ξ => ∫ y, ‖F ξ y‖ ∂(μ.restrict 𝓕) := by
    simp only [hnorm, integral_const, smul_eq_mul]
    have hr : (μ.restrict 𝓕).real Set.univ = 1 := by simp [Measure.real, hμ.2.2]
    simp only [hr, one_mul]
    exact GlobalTheory.SiegelWeilLitCompare.summable_rat hθ ⟨Φ, hΦ⟩
  show Φ 0 = ∫ y in 𝓕, ∑' ξ, F ξ y ∂μ
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [hF, integral_mul_const, char_integral hψ V hμ]
  rw [tsum_eq_single 0]
  · simp
  · intro b hb
    simp [hb]

end GlobalTheory.CompanionTheory.EisZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSocleSegmentProduct
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegSocle

theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (_root_.GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ).comp Fin.rev_injective

theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  rw [Set.ncard_le_one_iff_subsingleton]
  intro e₁ h₁ e₂ h₂
  ext a
  have i₁ := dec_injective hA Δ (h₁ a)
  have i₂ := dec_injective hA Δ (h₂ a)
  rw [← i₁, ← i₂]

theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.SegSocle

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLevelSubgroupsExist
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.PositionTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem eventually_factor {S : Set (Pl E)} {P : Slot S → Prop}
    (h₁ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S, P (Sum.inl ⟨w, hw⟩))
    (h₂ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S ∧ IsSplitAt w, P (Sum.inr ⟨w, hw⟩)) :
    ∀ᶠ i : Slot S in cofinite, P i := by
  have f₁ := Filter.eventually_cofinite.1 h₁
  have f₂ := Filter.eventually_cofinite.1 h₂
  refine Filter.eventually_cofinite.2 ?_
  refine (((f₁.preimage (Subtype.val_injective (p := fun w => w ∈ S)).injOn).image Sum.inl).union
    ((f₂.preimage (Subtype.val_injective (p := fun w => w ∈ S ∧ IsSplitAt w)).injOn).image Sum.inr)).subset ?_
  rintro (⟨w, hw⟩ | ⟨w, hw⟩) hi
  · exact Or.inl ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩
  · exact Or.inr ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩

def localLevel {S : Set (Pl E)} (L₁ L₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)
  | .inl w => L₁ w.1
  | .inr w => L₂ w.1

theorem exists_factor_level₂ {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  obtain ⟨L₁, o₁, e₁, i₁⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₂
  have c₁ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁
  have c₂ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂
  refine ⟨localLevel L₁ L₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (w | w)
    · exact o₁ w.1
    · exact o₂ w.1
  · exact eventually_factor (e₁.mono fun w h _ => h) (e₂.mono fun w h _ => h)
  · rintro (w | w) k hk x
    · exact (i₁ w.1 k hk x).2
    · exact (i₂ w.1 k hk x).2
  · rintro (w | w)
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₁ w.1
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₂ w.1
  · exact eventually_factor (c₁.mono fun w h _ => h) (c₂.mono fun w h _ => h)

end GlobalTheory.CompanionTheory.PositionTest

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSMx
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswTop

theorem topC : PositivityTheory.Rg.Rsw.Cell.TopC := by
  intro D p e
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D p e
  exact ⟨inferInstance, inferInstance, inferInstance, h2, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.RswTop
end
end

