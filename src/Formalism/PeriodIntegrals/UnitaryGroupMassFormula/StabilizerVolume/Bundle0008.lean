module

public import Mathlib
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
public import Formalism.PeriodIntegrals.Bundle0019

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HformSmulRight
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

@[reducible] def starOfInv {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by
    show σ (x * y) = σ y * σ x
    rw [map_mul, mul_comm]
  star_add x y := map_add σ x y

section General

variable {E : Type} [Field E] {M : ℕ}

theorem hform_add_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J (c • x) y = σ c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J x (c • y) = RingHom.id E c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable [StarRing E]

def hSes (J : Matrix (Fin M) (Fin M) E) : (Fin M → E) →ₗ⋆[E] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (hform_add_left' _ J) (hform_smul_left' _ J) (hform_add_right' _ J) (hform_smul_right' _ J)

theorem hSes_apply (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hSes J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hSes_herm (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (x y : Fin M → E) : star (hSes J x y) = hSes J y x := by
  rw [hSes_apply, hSes_apply]
  show starRingEnd E _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem hSes_nondeg (J : Matrix (Fin M) (Fin M) E) (hdet : J.det ≠ 0) (x : Fin M → E)
    (hx : ∀ y, hSes J x y = 0) : x = 0 := by
  have h1 : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have := hx (Pi.single j 1)
    rw [hSes_apply] at this
    simpa [Formalism.UG.hform, Pi.single_apply, vecMul, dotProduct] using this
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  have := congrFun h2 i
  simpa using this

theorem linInd_of_gram (J : Matrix (Fin M) (Fin M) E) {a : ℕ} (X : Fin a → Fin M → E)
    (G : Matrix (Fin a) (Fin a) E) (hG : ∀ i j, G i j = Formalism.UG.hform (starRingEnd E) J (X i) (X j))
    (hdet : G.det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : G *ᵥ c = 0 := by
    funext j
    have := congrArg (hSes J (X j)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [mulVec, dotProduct, Pi.zero_apply, hG]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSes_apply]
    ring
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h1) i

variable [CharZero E]

theorem witt_tuple (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (hdet : J.det ≠ 0) {a : ℕ} (X0 X : Fin a → Fin M → E) (h0 : LinearIndependent E X0)
    (h1 : LinearIndependent E X)
    (hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j)) :
    ∃ g ∈ Formalism.UG.UJ (starRingEnd E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E) *ᵥ X0 i = X i := by
  let U := Submodule.span E (Set.range X0)
  let bU : Module.Basis (Fin a) E U := Module.Basis.span h0
  have hb : ∀ i, ((bU i : U) : Fin M → E) = X0 i := fun i => by
    show ((Module.Basis.span h0 i : U) : Fin M → E) = X0 i
    rw [Module.Basis.span_apply]
  let f : U →ₗ[E] (Fin M → E) := bU.constr E X
  have hf : ∀ i, f (bU i) = X i := fun i => bU.constr_basis E X i
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hs := bU.sum_repr u
    rw [← hs] at hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hf] at hu
    have hc := (Fintype.linearIndependent_iff.mp h1) _ hu
    rw [← hs]
    simp [hc]
  have key : ((hSes J).comp f).compl₂ f = ((hSes J).comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis bU bU fun i j => ?_
    show hSes J (f (bU i)) (f (bU j)) = hSes J ((bU i : U) : Fin M → E) ((bU j : U) : Fin M → E)
    rw [hf, hf, hb, hb]
    exact hG i j
  have hiso : ∀ x y : U, hSes J (f x) (f y) = hSes J x y := fun x y =>
    DFunLike.congr_fun (DFunLike.congr_fun key x) y
  obtain ⟨g, hgiso, hgf⟩ :=
    witt_extension_theorem E (Fin M → E) (hSes J) (hSes_herm J hJ) (hSes_nondeg J hdet) U f hinj hiso
  let m : Matrix (Fin M) (Fin M) E := LinearMap.toMatrix' (g : (Fin M → E) →ₗ[E] (Fin M → E))
  let mi : Matrix (Fin M) (Fin M) E :=
    LinearMap.toMatrix' (g.symm : (Fin M → E) →ₗ[E] (Fin M → E))
  have hc1 : (g : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hc2 : (g.symm : (Fin M → E) →ₗ[E] (Fin M → E)).comp (g : (Fin M → E) →ₗ[E] (Fin M → E)) =
      LinearMap.id := LinearMap.ext fun x => by simp
  have hm1 : m * mi = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc1, LinearMap.toMatrix'_id]
  have hm2 : mi * m = 1 := by
    simp only [m, mi]
    rw [← LinearMap.toMatrix'_comp, hc2, LinearMap.toMatrix'_id]
  have hmv : ∀ v, m *ᵥ v = g v := fun v => by
    simp only [m]
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  refine ⟨⟨m, mi, hm1, hm2⟩, ?_, ?_⟩
  · show Formalism.UG.cT (starRingEnd E) m * J * m = J
    ext i j
    have h := hgiso (Pi.single i 1) (Pi.single j 1)
    rw [hSes_apply, hSes_apply, ← hmv, ← hmv, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single,
      Formalism.UG.P.hform_single] at h
    exact h
  · intro i
    show m *ᵥ X0 i = X i
    rw [hmv, ← hb i]
    exact (hgf (bU i)).trans (hf i)

end General

theorem sigma_invol_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem witt_holds : Witt := by
  unfold Witt InCtx
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ hdet X hX
  letI : StarRing E := starOfInv (σ : E →+* E) (sigma_invol_cm σ hCM)
  have hs : starRingEnd E = (σ : E →+* E) := RingHom.ext fun _ => rfl
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := by
    rw [hs]; exact hJ.1
  have hG : ∀ i j, Formalism.UG.hform (starRingEnd E) J (X i) (X j) =
      Formalism.UG.hform (starRingEnd E) J (X0 i) (X0 j) := by
    rw [hs]; exact fun i j => congrFun (congrFun hX i) j
  have hl0 : LinearIndependent E X0 :=
    linInd_of_gram J X0 (gramE σ J X0) (by rw [hs]; intro i j; rfl) hdet
  have hl1 : LinearIndependent E X :=
    linInd_of_gram J X (gramE σ J X) (by rw [hs]; intro i j; rfl) (hX ▸ hdet)
  obtain ⟨g, hg, hgX⟩ := witt_tuple J hJ' hJ.2 X0 X hl0 hl1 hG
  rw [hs] at hg
  exact ⟨g, hg, hgX⟩

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProd
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def LocEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    ∃ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E))
      (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf ∧ SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf ∧
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) ∧
      (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) ∧
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf ∧
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)

def SdUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ1 μ2, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ1 → SdW F E σ M J (Ainf F) (psiInf F ψ) a μ2 →
      μ1 = μ2) ∧
    (∀ ν1 ν2, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν1 → SdHerm F E σ (Ainf F) (psiInf F ψ) a ν2 →
      ν1 = ν2) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ μ1 μ2, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ1 → SdW F E σ M J (Fv F v) (psiV F ψ v) a μ2 →
        μ1 = μ2) ∧
      (∀ ν1 ν2, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν1 →
        SdHerm F E σ (Fv F v) (psiV F ψ v) a ν2 → ν1 = ν2)

def FibPin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
      ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      ∀ fib1 fib2 : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib1 →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib2 →
      ∀ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf → HasCompactSupport Φinf →
        ∫ X, Φinf X ∂(fib1 (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fib2 (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
      ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      ∀ fib1 fib2 : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib1 →
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib2 →
      ∀ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv →
        ∫ X, Φv X ∂(fib1 (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv X ∂(fib2 (hermOf (Fv F v) σ (gramE σ J X0) hT))

def MultFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))

def RestrProd : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    ∃ νX : Measure (Fin a → Fin M → AF F ⊗[F] E),
      νX {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} = 0 ∧
      ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
        (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
        Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
        Integrable Φ νX ∧
        ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
          ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))

theorem exOmT_of (h1 : LocEx) (h2 : SdUniq) (h3 : FibPin) (h4 : MultFib) (h5 : RestrProd) :
    ExOmT := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c1 := h1 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c2 := h2 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c3 := h3 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c4 := h4 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c5 := h5 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μinf, νinf, μv, νv, fibInf, fibV, hμi, hνi, hμv, hνv, hfi, hfv⟩ := c1
  obtain ⟨νX, hsupp, hform⟩ :=
    c5 μinf hμi νinf hνi μv hμv νv hνv fibInf hfi fibV hfv (c4 μv hμv νv hνv fibV hfv)
  refine ⟨νX, hsupp, ⟨μinf, hμi⟩, fun μinf' hμi' => ?_⟩
  obtain rfl := c2.1 _ _ hμi hμi'
  refine ⟨⟨νinf, hνi⟩, fun νinf' hνi' => ?_⟩
  obtain rfl := c2.2.1 _ _ hνi hνi'
  refine ⟨⟨μv, hμv⟩, fun μv' hμv' => ?_⟩
  obtain rfl : μv = μv' := funext fun v => (c2.2.2 v).1 _ _ (hμv v) (hμv' v)
  refine ⟨⟨νv, hνv⟩, fun νv' hνv' => ?_⟩
  obtain rfl : νv = νv' := funext fun v => (c2.2.2 v).2 _ _ (hνv v) (hνv' v)
  refine ⟨⟨fibInf, hfi⟩, fun fibInf' hfi' => ⟨⟨fibV, hfv⟩, fun fibV' hfv' => ?_⟩⟩
  intro d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  obtain ⟨hI, hF⟩ := hform d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  refine ⟨hI, c4 μv hμv νv hνv fibV' hfv' d b Φf Φv hp, ?_⟩
  rw [hF, c3.1 μinf hμi νinf hνi fibInf fibInf' hfi hfi' Φinf hc1 hc2]
  congr 1
  exact tprod_congr fun v => c3.2 v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (fibV' v) (hfv v)
    (hfv' v) (Φv v) (hp.1 v)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWOf
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem volStabFromSW_of (h1 : ExChar) (h2 : ExOmT) (h3 : ExStab) (h4 : ExFDStab)
    (h5 : SWeqOm) (h6 : Unfold) (h7 : PosTest) : PI.VolStabS.VolStabFromSWS := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet
  refine ⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩
  refine ⟨ha.1, fun μ hμ => ?_⟩
  refine ⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩
  refine ⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩
  obtain ⟨hμ'H, hμ'C⟩ := hμ'
  refine ⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩
  refine ⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩
  obtain ⟨φ, hφ0, hadm, hI⟩ := h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  have e1 := h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  unfold meanC at e1
  have hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ))
      {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    exact hI e1.symm
  obtain ⟨hfin, e2⟩ :=
    h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕'
      φ hφ0 hadm.adm hθ
  rw [e2, smul_smul] at e1
  have hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1 := by
    have e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX =
        1 * ∫ X, (φ X : ℂ) ∂νX := by
      rw [one_mul, ← Complex.real_smul]
      exact e1
    exact_mod_cast mul_right_cancel₀ hI e3
  have h0 : (μ 𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hc1
    exact zero_ne_one hc1
  have e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal := (inv_mul_eq_one₀ h0).1 hc1
  exact (ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm

end PI.VolStabS
end
end

