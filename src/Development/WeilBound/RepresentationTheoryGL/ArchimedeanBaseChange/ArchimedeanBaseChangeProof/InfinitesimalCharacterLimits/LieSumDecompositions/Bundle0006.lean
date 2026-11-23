module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksExp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def tl (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tl_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) : (tl r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    show f (aT E N r s * (aT E N r (s * i) * g)) = f (aT E N r (s * ((i + 1 : ℕ) : ℝ)) * g)
    rw [← mul_assoc, ← aT_add, show s + s * (i : ℝ) = s * ((i + 1 : ℕ) : ℝ) by push_cast; ring]

theorem kl_iff (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Kl r s p F ↔ aeval (tl r s) p F = 0 := by
  have e : aeval (tl (N := N) r s) p F = fun g => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) := by
    rw [aeval_eq_sum_range, LinearMap.sum_apply]
    funext g
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, tl_pow]
    rfl
  rw [e]
  constructor
  · intro h
    funext g
    exact h g
  · intro h g
    exact congrFun h g

theorem kl_mul {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) : Kl r s (p * q) F := by
  rw [kl_iff] at h ⊢
  rw [mul_comm, aeval_mul, Module.End.mul_apply, h, map_zero]

theorem kl_mul' {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s q F) : Kl r s (p * q) F := by
  rw [mul_comm]
  exact kl_mul h

theorem ctn_eq_ct (r : ℕ) :
    letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
    ∃ μ : Measure (BlockIx N r → Ad E), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E N r) (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) μ ∧
      ∀ f : Sm E N, An.ctn r f.1 = PositivityTheory.Affgl.CT.ct μ (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) f.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  refine ⟨μ, hμ, hD, fun f => funext fun g => ?_⟩
  show An.ctn r f.1 g = ∫ x in GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r, f.1 (unip x * g) ∂μ
  rw [hint]
  simp only [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem ctn_add (r : ℕ) {φ ψ : Sm E N} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) :
    An.ctn r (φ + ψ).1 = An.ctn r φ.1 + An.ctn r ψ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, e⟩ := ctn_eq_ct (E := E) (N := N) r
  have := hμ
  rw [e, e, e]
  exact ct_add μ _ hD hφ hψ

theorem ctn_smul (r : ℕ) (c : ℂ) (φ : Sm E N) : An.ctn r (c • φ).1 = c • An.ctn r φ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨μ, -, -, e⟩ := ctn_eq_ct (E := E) (N := N) r
  rw [e, e]
  exact ct_smul μ _ c φ

def Good (β : ℕ → ℝ) (φ : Sm E N) : Prop :=
  IsAutForm φ ∧ ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ Kl r 1 p (An.ctn r φ.1) ∧ ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (β r)

theorem good_bound {β : ℕ → ℝ} {φ : Sm E N} (h : Good β φ) :
    ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro r hr hrN c hc
  obtain ⟨p, -, hk, hroot⟩ := h.2 r hr hrN
  obtain ⟨F₀, hCT, F, hFspan, hF0, hFe⟩ := hc
  obtain ⟨-, -, -, hD⟩ := dict_holds E N
  obtain ⟨c₁, -, e₁⟩ := (hD φ h.1 r hr hrN).2 F₀ hCT
  have hk₀ : Kl r 1 p F₀ := by
    have : F₀ = c₁ • An.ctn r φ.1 := by
      funext g
      rw [e₁]
      rfl
    rw [this]
    exact (klSub r 1 p).smul_mem c₁ hk
  have hroot' := kl_eigen (kl_span hk₀ hFspan) hF0 hFe
  have h1 := hroot (Complex.exp (c * ((1 : ℝ) : ℂ))) hroot'
  rw [Complex.norm_exp] at h1
  have h2 := Real.exp_le_exp.1 h1
  simpa using h2

theorem good_of (β : ℕ → ℝ) {φ : Sm E N} (hφ : IsAutForm φ)
    (hexp : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) : Good β φ := by
  refine ⟨hφ, fun r hr hrN => ?_⟩
  obtain ⟨hA, -, -, hCT⟩ := dict_holds E N
  have hct := (hCT φ hφ r hr hrN).1
  have hfin := finTr_holds E N φ hφ r hr hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => aT_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp (GlobalTheory.CompanionTheory.ContAutForm.continuous_of_isAutForm_totallyComplex E N φ hφ) r
      ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [one_mul] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    have hc : c ∈ Exp r φ.1 := ⟨_, hct, F, hF, hF0, hFe⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hexp r hr hrN c hc)

theorem good_add {β : ℕ → ℝ} {φ ψ : Sm E N} (hφ : Good β φ) (hψ : Good β ψ) : Good β (φ + ψ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hφ.1 hψ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  obtain ⟨q, hq, hqk, hqr⟩ := hψ.2 r hr hrN
  refine ⟨p * q, hp.mul hq, ?_, fun z hz => ?_⟩
  · rw [ctn_add r hφ.1 hψ.1]
    exact (klSub r 1 (p * q)).add_mem (kl_mul hpk) (kl_mul' hqk)
  · rcases (Polynomial.root_mul.1 hz) with h | h
    · exact hpr z h
    · exact hqr z h

theorem good_smul {β : ℕ → ℝ} {φ : Sm E N} (hφ : Good β φ) (c : ℂ) : Good β (c • φ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul c hφ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  refine ⟨p, hp, ?_, hpr⟩
  rw [ctn_smul]
  exact (klSub r 1 p).smul_mem c hpk

theorem good_zero (β : ℕ → ℝ) : Good β (0 : Sm E N) := by
  refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun r hr hrN => ⟨1, monic_one, ?_, fun z hz => ?_⟩⟩
  · have e : An.ctn r (0 : Sm E N).1 = (0 : ℂ) • An.ctn r (0 : Sm E N).1 := by
      rw [← ctn_smul, zero_smul]
    rw [e]
    exact (klSub r 1 1).smul_mem 0 (by
      intro g
      simp [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm])
  · exact absurd hz (by simp [Polynomial.IsRoot])

theorem exp_span (S : Set (Sm E N)) (β : ℕ → ℝ) (haut : ∀ φ ∈ S, IsAutForm φ)
    (hexp : ∀ φ ∈ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) :
    ∀ φ ∈ Submodule.span ℂ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro φ hφ
  refine good_bound ?_
  induction hφ using Submodule.span_induction with
  | mem x hx => exact good_of β (haut x hx) (hexp x hx)
  | zero => exact good_zero β
  | add x y _ _ hx hy => exact good_add hx hy
  | smul c x _ hx => exact good_smul hx c

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksSl
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem zalg_comm {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) : ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add (f := _), e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∈ S := fun τ u φ hφ =>
    ⟨Zalg_stable hI (cap_mem_Zalg τ u) φ hφ, GlobalTheory.SpehInfChar.cap_comm_quot hI f hf τ u φ hφ⟩
  have hle : Zalg E N ≤ S := Algebra.adjoin_le (by rintro _ ⟨τ, u, rfl⟩; exact hcap τ u)
  exact hle hz

variable {r s : ℕ}

theorem expand {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) : ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ Submodule.span ℂ (lsF r s (T ψ) k g)) ∧
        (∀ i, q i ∈ rsF r s (T ψ) k g) ∧
        ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  intro ψ hψ k g
  have hAψ : IsAutForm ψ := hU.2 ψ hψ
  have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ

  let L := GlobalTheory.DiscClosure.stabSub ψ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAψ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T ψ) = T ψ := fun h hh => by
    have e := hT.equiv (.fin h) ψ hψ
    have hh' : finRep E (r + s) h ψ = ψ := hh
    change T (finRep E (r + s) h ψ) = finRep E (r + s) h (T ψ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T ψ)
  have : FiniteDimensional ℂ S := by
    have := hAψ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ ψ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) ψ hψ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T ψ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g' : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T ψ)).1 g') ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g' =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T ψ, Submodule.subset_span ⟨1, by simp⟩⟩ g'

  have := hAψ.zfin
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z ψ = 0}
  have hJ : Cofin J := PositivityTheory.Rg.Rs.JFinTr.cofin_ann ψ
  have hJZ : J ⊆ Zalg E (r + s) := fun z hz => hz.1
  have hZ : ∀ z ∈ J, z (T ψ) = 0 := by
    rintro z ⟨hz, hzψ⟩
    rw [← (zalg_comm hI T hT.equiv hz ψ hψ).2, hzψ, map_zero]
  obtain ⟨J₁, -, c₁, -, k₁, -⟩ := centre J hJ

  let L₁ := Slice1.levelOne s L g
  let ρ₁ := ρ.comp (Slice1.levK E r s)
  have := PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁
    (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁
  let S₁ := Submodule.span ℂ (lsF r s (T ψ) k g) ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)
  have : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le inf_le_right
  let U' := S₁.map (Sm E r).subtype
  obtain ⟨P, a, ha⟩ := SliceTensor.interp U'
  let f : GA E r × GA E s → ℂ := fun m => (T ψ).1 (lev (Ad E) r s m * yp k g)
  have hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U' := by
    intro m₂
    obtain ⟨ψ₁, hψA, hψ₁, -⟩ := hT.left ψ hψ k g m₂
    have hmem : ψ₁ ∈ genSpace L₁ ρ₁ J₁ := by
      refine SliceTensor.slice_mem ρ hJZ k₁ (T ψ) (hT.unipInv ψ hψ) hLv hC hZ g k m₂ ψ₁ hψA fun m₁ => ?_
      rw [hψ₁, infGL_comm, mul_assoc]
    have hls : ψ₁ ∈ lsF r s (T ψ) k g := ⟨m₂, fun m₁ => hψ₁ m₁⟩
    exact ⟨ψ₁, ⟨Submodule.subset_span hls, Submodule.subset_span hmem⟩, funext fun m₁ => hψ₁ m₁⟩
  have hb : ∀ κ : P, ∃ b ∈ Submodule.span ℂ (lsF r s (T ψ) k g), b.1 = (a κ : GA E r → ℂ) := by
    intro κ
    obtain ⟨b, hb, e⟩ := (a κ).2
    exact ⟨b, hb.1, e⟩
  choose b hbm hbe using hb
  have hright : ∀ κ : P, ∃ ψ₂ ∈ rsF r s (T ψ) k g, ∀ m₂, ψ₂.1 m₂ = f (κ.1, m₂) := by
    intro κ
    obtain ⟨ψ₂, -, e, -⟩ := hT.right ψ hψ k g κ.1
    exact ⟨ψ₂, ⟨κ.1, fun m₂ => e m₂⟩, e⟩
  choose q hqm hqe using hright
  have hf : ∀ m : GA E r × GA E s, f m = ∑ κ : P, (b κ).1 m.1 * (q κ).1 m.2 := by
    intro m
    have e := congrFun (ha _ (hleft m.2)) m.1
    rw [Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun κ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hbe, hqe]
    ring
  let eP := (Fintype.equivFin P).symm
  refine ⟨Fintype.card P, fun i => b (eP i), fun i => q (eP i), fun i => hbm _, fun i => hqm _, fun m => ?_⟩
  rw [show (T ψ).1 (lev (Ad E) r s m * yp k g) = f m from rfl, hf m]
  exact (Equiv.sum_comp eP (fun κ => (b κ).1 m.1 * (q κ).1 m.2)).symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogQ
section
noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M] (V I : Submodule ℂ M)

def Pa : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {T | (∀ v ∈ V, T v ∈ V) ∧ ∀ v ∈ I, T v ∈ I}
  mul_mem' := fun {_ _} hS hT => ⟨fun v hv => hS.1 _ (hT.1 v hv), fun v hv => hS.2 _ (hT.2 v hv)⟩
  add_mem' := fun {_ _} hS hT => ⟨fun v hv => V.add_mem (hS.1 v hv) (hT.1 v hv), fun v hv => I.add_mem (hS.2 v hv) (hT.2 v hv)⟩
  algebraMap_mem' := fun c => ⟨fun _ hv => V.smul_mem c hv, fun _ hv => I.smul_mem c hv⟩

def piQ : Pa V I →ₐ[ℂ] Module.End ℂ (V ⧸ I.comap V.subtype) where
  toFun T := (I.comap V.subtype).mapQ (I.comap V.subtype) (T.1.restrict T.2.1) (fun v hv => T.2.2 _ hv)
  map_one' := by
    ext v
    rfl
  map_mul' S T := by
    ext v
    rfl
  map_zero' := by
    ext v
    rfl
  map_add' S T := by
    ext v
    rfl
  commutes' c := by
    ext v
    rfl

theorem piQ_eq_zero {T : Pa V I} (h : piQ V I T = 0) : ∀ v ∈ V, T.1 v ∈ I := by
  intro v hv
  have e := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨v, hv⟩)
  rw [LinearMap.zero_apply] at e
  change Submodule.Quotient.mk (T.1.restrict T.2.1 ⟨v, hv⟩) = 0 at e
  rw [Submodule.Quotient.mk_eq_zero] at e
  exact e

theorem piQ_eq_algebraMap {T : Pa V I} (c : ℂ) (h : ∀ v ∈ V, T.1 v - c • v ∈ I) : piQ V I T = algebraMap ℂ _ c := by
  ext v
  change Submodule.Quotient.mk (T.1.restrict T.2.1 v) = Submodule.Quotient.mk (c • v)
  rw [Submodule.Quotient.eq]
  exact h v.1 v.2

end Quot

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def Sl (N : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E N)) := Algebra.adjoin ℂ (Set.range (lie E N))

theorem lie_mem_Sl {N : ℕ} (X : Lie E N) : lie E N X ∈ Sl (E := E) N := Algebra.subset_adjoin ⟨X, rfl⟩

theorem Eop_mem_Sl {N : ℕ} (τ : E →+* ℂ) (i j : Fin N) : Eop τ i j ∈ Sl (E := E) N := by
  have h1 : lieS E N i j (atEmb τ 1) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have h2 : lieS E N i j (atEmb τ Complex.I) ∈ Sl (E := E) N := by rw [lieS_apply]; exact lie_mem_Sl _
  have e : Eop τ i j = (1 / 2 : ℂ) • (lieS E N i j (atEmb τ 1) - Complex.I • lieS E N i j (atEmb τ Complex.I)) := rfl
  rw [e]
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 (Subalgebra.smul_mem _ h2 _)) _

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) {n : ℕ} (X : Fin n → Fin n → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hX _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem Sl_comm_cap {N : ℕ} (τ : E →+* ℂ) (u : ℂ) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (cap τ u) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {cap (a := N) τ u} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

theorem Sl_comm_ltr {N : ℕ} (h : GA E N) {T : Module.End ℂ (Sm E N)} (hT : T ∈ Sl N) :
    Commute (JFinTr.ltr h) T := by
  have hle : Sl (E := E) N ≤ Subalgebra.centralizer ℂ {JFinTr.ltr h} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨X, rfl⟩
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro y rfl
    exact (JFinTr.ltr_lie h X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

