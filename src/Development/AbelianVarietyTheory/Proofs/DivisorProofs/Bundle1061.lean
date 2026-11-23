module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zeta_eval {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μW : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μW 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ) (v : M.Vec) (K : Subgroup (GA D W))
    {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓧 : Set X) (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (φ f : X → ℂ)
    (Fr : Frames W) (hFr : ∀ ρ b, realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (mR : ∀ ρ, Measure (Upq W ρ))
    (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (c0 z : ℂ)
    (hF : ∀ x ∈ GfC W, ∀ g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) →
      l2 μ 𝓧 (ω (1, x * realElt θ W g) φ) φ =
        c0 * (∏ ρ, ⟪(v ρ : M.H ρ), M.rep ρ (g ρ) (v ρ : M.H ρ)⟫_ℂ) * 1 * l2 μ 𝓧 (ω (1, x) f) f)
    (hZ : ∀ v₁ v₂ : M.Vec, HasSum (fun y : FinCos W K =>
        l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (l2 μW 𝓖 (rTr W y.rep (HW.e U₁ v₁)) (HW.e U₂ v₂)))
      (z * starRingEnd ℂ (l2 μW 𝓖 (HW.e U₁ v₁) (HW.e U₂ v₂)))) :
    ∫ b : ∀ ρ, Upq W ρ, ∑' x : FinCos W K, l2 μ 𝓧 (ω (1, x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) φ) φ *
        starRingEnd ℂ (l2 μW 𝓖 (rTr W (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) (HW.e U₁ v)) (HW.e U₂ v))
        ∂(Measure.pi mR) =
      c0 * z * starRingEnd ℂ (ipM M μW 𝓖 (HW.e U₂) (HW.e U₁)) *
        ((∏ ρ, ∫ b, ‖⟪(v ρ : M.H ρ), M.rep ρ (realMat W Fr ρ b) (v ρ : M.H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) : ℝ) : ℂ) := by
  have hIP : IsMultIP M μW 𝓖 (HW.e U₂) (HW.e U₁) (ipM M μW 𝓖 (HW.e U₂) (HW.e U₁)) := by
    have existsIP (x y : HW.H) (hxy : inner ℂ x y ≠ 0) : ∃ c, IsMultIP M μW 𝓖 (HW.e x) (HW.e y) c := by
      by_contra h
      apply hxy
      rw [hW, ipM, dite_eq_right h, mul_zero]
    apply ipM_spec
    by_cases hx : U₂ = 0
    · subst U₂
      exact ⟨0, fun v₁ v₂ => by simp⟩
    by_cases hxy : inner ℂ U₂ U₁ = 0
    · obtain ⟨c, hc⟩ := existsIP U₂ (U₂ + U₁) (by
        rw [inner_add_right, hxy, add_zero]
        exact inner_self_ne_zero.2 hx)
      obtain ⟨c', hc'⟩ := existsIP U₂ U₂ (inner_self_ne_zero.2 hx)
      refine ⟨c - c', fun v₁ v₂ => ?_⟩
      have hsub : (fun x => star (HW.e U₂ v₁ x) * HW.e U₁ v₂ x) =
          fun x => star (HW.e U₂ v₁ x) * HW.e (U₂ + U₁) v₂ x - star (HW.e U₂ v₁ x) * HW.e U₂ v₂ x := by
        funext x
        simp [mul_add]
      rw [hsub]
      exact ⟨(hc v₁ v₂).1.sub (hc' v₁ v₂).1, by
        rw [integral_sub (hc v₁ v₂).1 (hc' v₁ v₂).1, (hc v₁ v₂).2, (hc' v₁ v₂).2, sub_mul]⟩
    · exact existsIP U₂ U₁ hxy
  have := fun ρ => sigmaFinite_haar (mR ρ) (hmR ρ).1
  refine integral_pi_eval mR (fun ρ b => ⟪(v ρ : M.H ρ), M.rep ρ (realMat W Fr ρ b) (v ρ : M.H ρ)⟫_ℂ) _ c0 z _ fun b => ?_
  let g := fun ρ => realMat W Fr ρ (b ρ)
  have hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) := fun ρ => hFr ρ (b ρ)
  let w : M.Vec := fun ρ => ⟨_, rep_mem_sm M ρ (g ρ) (hg ρ) _ (v ρ).2⟩
  have hTranslate (U : MMap M) (hU : U ∈ Mult θ M J χ) : U w = rTr W (realElt θ W g) (U v) := by
    classical
    induction hU using Submodule.span_induction with
    | mem U hU =>
      change IsMultMap θ M J χ U at hU
      have hList (l : List D.what₂.Tau) (hl : l.Nodup) :
          U (fun ρ => if ρ ∈ l then w ρ else v ρ) =
            rTr W (l.map fun ρ => atTau θ W ρ (g ρ)).prod (U v) := by
        induction l with
        | nil =>
          funext x
          simp [rTr]
        | cons a l ih =>
          rw [List.nodup_cons] at hl
          have he := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
            simp only [ite_eq_right hl.1]
            rfl)
          rw [ih hl.2] at he
          rw [List.map_cons, List.prod_cons, rTr_mul, ← he]
          congr 1
          funext ρ
          by_cases hρ : ρ = a
          · subst hρ
            simp
          · rw [Function.update_of_ne hρ]
            simp [hρ]
      unfold realElt
      rw [← hList _ (Finset.nodup_toList _)]
      congr 1
      funext ρ
      simp
    | zero =>
      funext x
      simp [rTr]
    | add U U' _ _ h₁ h₂ =>
      funext x
      have he₁ := congrFun h₁ x
      have he₂ := congrFun h₂ x
      simp only [rTr, add_apply, Pi.add_apply] at he₁ he₂ ⊢
      rw [he₁, he₂]
    | smul c U _ h =>
      funext x
      have he := congrFun h x
      simp only [rTr, smul_apply, Pi.smul_apply] at he ⊢
      rw [he]
  have h2 : l2 μW 𝓖 (HW.e U₁ w) (HW.e U₂ v) =
      ipM M μW 𝓖 (HW.e U₂) (HW.e U₁) * ∏ ρ, ⟪(v ρ : M.H ρ), M.rep ρ (g ρ) (v ρ : M.H ρ)⟫_ℂ :=
    (l2_eq_star μW 𝓖 _ _).trans (hIP v w).2
  rw [← h2]
  refine tsum_eval _ _ _ _ _ (fun x => ?_) (hZ w v)
  rw [hF x.rep x.out.2 _ hg, rTr_mul, ← hTranslate (HW.e U₁) hU]

theorem eventually_grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), ∃ h : (finHom V).rangeRestrict κ ∈ grpOf V β L, chrOf V β L ⟨_, h⟩ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  have hk : Lev.finE V κ ∈ lev D.sp.cm V.gram β L :=
    Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩
  exact ⟨hk, GlobalTheory.ThetaIntegrand.levFn_eq_one β (Lev.finE V κ) L (fun PP hP => h3 PP (Finset.mem_union_left _ hP))
    fun PP hP => h3 PP (Finset.mem_union_right _ hP)⟩


open scoped ComplexOrder in
theorem integrableOn_lift {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω) (hs : V.SigOK)
    (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w)) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V K ν 𝓕) (g : GA D W) :
    IntegrableOn (fun h => Datum.thetaKO ω h g (φ (c.ext x h))) 𝓕 ν := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hω.std V W χS χT ω hω hpos c.W φ hφ _
    (GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1 (eventually_grpOf V β L) hx)
    (GlobalTheory.ThetaIntegrand.ext_invariant c hx) ν 𝓕 hν.1.1 hν.2 g

theorem exists_linear_lift {X X' Y B W Z κ₁ κ₂ : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    [AddCommGroup Y] [Module ℂ Y] [MeasurableSpace B]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z] (ν : Measure B) (𝓕 : Set B) (e : Y →ₗ[ℂ] Z)
    (val : κ₁ → κ₂ → Z → ℂ) (hadd : ∀ a b z z', val a b (z + z') = val a b z + val a b z')
    (hsm : ∀ a b (t : ℂ) z, val a b (t • z) = t * val a b z)
    (E₁ : X →ₗ[ℂ] X') (E₂ : X' →ₗ[ℂ] (B → W)) (k : κ₁ → κ₂ → B → W → ℂ)
    (kadd : ∀ a b h z z', k a b h (z + z') = k a b h z + k a b h z') (ksm : ∀ a b h (t : ℂ) z, k a b h (t • z) = t * k a b h z)
    (hint : ∀ x a b, IntegrableOn (fun h => k a b h (E₂ (E₁ x) h)) 𝓕 ν)
    (hex : ∀ x, ∃ y, ∀ a b, val a b (e y) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν) :
    ∃ th : X →ₗ[ℂ] Y, ∀ x a b, IntegrableOn (fun h => k a b h (E₂ (E₁ x) h)) 𝓕 ν ∧
      val a b (e (th x)) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν := by
  have k0 : ∀ a b h, k a b h 0 = 0 := fun a b h => by simpa using ksm a b h 0 0
  obtain ⟨th, h⟩ := exists_linear_section (fun x y => ∀ a b, val a b (e y) = ∫ h in 𝓕, k a b h (E₂ (E₁ x) h) ∂ν)
    (fun a b => by simpa [k0] using hsm a b 0 0)
    (fun x x' y y' h h' a b => by
      rw [map_add (f := _), hadd, h, h', ← integral_add (hint x a b) (hint x' a b)]
      simp only [map_add (f := _), Pi.add_apply, kadd])
    (fun t x y h a b => by
      rw [map_smul, hsm, h, ← integral_const_mul]
      simp only [map_smul, Pi.smul_apply, ksm]) hex
  exact ⟨th, fun x a b => ⟨hint x a b, h x a b⟩⟩

theorem form_algebra {κ : Type} [Fintype κ] (N Vol H P nrm dO J : ℝ) (E x y cb c0 : ℂ) (t : κ → ℂ) (hc : c0 = H)
    (hx : x = (N : ℂ) ^ 2 * ∑ k, t k) (ht : ∀ k, t k = (Vol : ℂ) * (c0 * ((P : ℂ) * (nrm : ℂ) * (E / (dO : ℂ))) * cb * (J : ℂ)))
    (hy : y = (N : ℂ) * cb) : x = (((P * (N * Fintype.card κ * Vol * H * nrm / dO * J) : ℝ) : ℂ) * E) * y := by
  rw [hx, hy]
  simp only [ht, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem scalar_adjLev {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) {X Y : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥) (a : ℝ) (E : ℂ) (ha : 0 < a * ‖E‖)
    (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') =
      (((((Nat.card P.H : ℕ) : ℝ) * a : ℝ) : ℂ) * E) * inner ℂ y y') :
    ∀ y ∈ U, th (adjLev P th y) = ((a * ‖E‖ : ℝ) : ℂ) • y := by
  intro y hy
  have hP : 0 < Nat.card P.H := Nat.card_pos
  have ha0 : 0 ≤ a := by
    by_contra hneg
    exact absurd ha (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hneg).le (norm_nonneg E)))
  rw [adjLev, LinearMap.smul_apply, map_smul, scalar_of_form th U hU _ h y hy, smul_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  congr 1
  have : ((Nat.card P.H : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  push_cast
  field_simp

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ptL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (u : X →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : X →ₗ[ℂ] (Datum.WO (Vc D i) (Wc D i) → ℂ) where
  toFun w := ptAt R i σ BW f (u w)
  map_add' w w' := by rw [map_add (f := _)]; exact map_add _ _ _
  map_smul' a w := by rw [map_smul]; exact map_smul _ _ _

theorem ptL_apply (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (f : Datum.WO (Vc D i) (Wc D i) → ℂ) {X : Type} [AddCommGroup X] [Module ℂ X]
    (u : X →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : X) : ptL R i σ BW f u w = ptAt R i σ BW f (u w) := rfl

variable {R} {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftData R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

end Main

end GlobalTheory.AdelicScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLe
section
set_option autoImplicit false

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_exp_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ),
    0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ,
    (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  intro G _ Λ B d _ hB hfin C hC ε hε
  set e : ℕ := max 1 ⌈C / ε⌉₊ with he_def
  have he1 : 1 ≤ e := le_max_left _ _
  have heR : (0 : ℝ) < e := by exact_mod_cast he1
  have he1R : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hCe : C ≤ ε * e := by
    have h1 : C / ε ≤ (⌈C / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈C / ε⌉₊ : ℝ) ≤ e := by exact_mod_cast le_max_right _ _
    rw [div_le_iff₀ hε] at h1
    nlinarith
  refine ⟨1 / e, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (3 * e)] with m hm hm3
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set R := Real.exp (1 / e * m) with hR
  have hR1 : 1 ≤ R := Real.one_le_exp (by positivity)
  set Q := ⌈2 * R + 1⌉₊ with hQdef
  have hQ : 2 * R + 1 ≤ Q := Nat.le_ceil _
  have hQ4 : (Q : ℝ) ≤ 4 * R := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * R + 1 by linarith)
    linarith
  have key := _root_.GlobalTheory.VolBr.encard_ball_pow_le G (Λ m) (B m) (hB m) R Q e hR1 hQ (hfin m R)
  have mono : ∀ r s : ℝ, r ≤ s → B m r ⊆ B m s := by
    intro r s hrs x hx
    have := (hB m).sub_mem r (s - r) x 0 hx ((hB m).zero_mem _ (by linarith))
    simpa using this
  have hRe : R ^ (e + 1) ≤ Real.exp (2 * m) := by
    rw [hR, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) / e ≤ m := div_le_self hm0 he1R
    have h3 : ((e + 1 : ℕ) : ℝ) * (1 / e * m) = m + m / e := by
      push_cast; field_simp
    rw [h3]; linarith
  have hbig : R * (Q : ℝ) ^ e ≤ Real.exp (3 * m) := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp 3; linarith
    have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    calc R * (Q : ℝ) ^ e ≤ R * (4 * R) ^ e := by gcongr
      _ = 4 ^ e * R ^ (e + 1) := by ring
      _ ≤ Real.exp 3 ^ e * Real.exp (2 * m) := by gcongr
      _ = Real.exp (3 * e + 2 * m) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * m) := by
        apply Real.exp_le_exp.mpr
        have : (3 * e : ℝ) ≤ m := by exact_mod_cast hm3
        linarith
  have hsub := mono _ _ hbig
  have hN : (B m R).ncard ^ e ≤ (B m 1).ncard ^ e * (B m (Real.exp (3 * m))).ncard := by
    rw [← (hfin m R).cast_ncard_eq, ← (hfin m 1).cast_ncard_eq, ← (hfin m _).cast_ncard_eq] at key
    norm_cast at key
    have hsub' : B m (R * ((Q ^ e : ℕ) : ℝ)) ⊆ B m (Real.exp (3 * m)) := by push_cast; exact hsub
    exact key.trans (Nat.mul_le_mul_left _ (Set.ncard_le_ncard hsub' (hfin m _)))
  have pos : ∀ r : ℝ, 0 ≤ r → (0 : ℝ) < (B m r).ncard := fun r hr => by
    exact_mod_cast (Set.ncard_pos (hfin m r)).mpr ⟨0, (hB m).zero_mem r hr⟩
  have hA := pos R (by linarith)
  have h1 := pos 1 zero_le_one
  have h3 := pos (Real.exp (3 * m)) (Real.exp_pos _).le
  have hNR : ((B m R).ncard : ℝ) ^ e ≤ ((B m 1).ncard : ℝ) ^ e * (B m (Real.exp (3 * m))).ncard := by
    exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity) hNR
  rw [Real.log_mul (by positivity) h3.ne', Real.log_pow, Real.log_pow] at hlog
  have hCm : C * (m : ℝ) ^ d ≤ ε * e * (m : ℝ) ^ d := mul_le_mul_of_nonneg_right hCe (pow_nonneg hm0 d)
  have : (e : ℝ) * Real.log ((B m R).ncard : ℝ) ≤
      e * (Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d) := by nlinarith
  exact le_of_mul_le_mul_left this heR

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCM
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.GlobHerm

theorem vandermonde_diag_herm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hl : Function.Injective l)
    (h1 : ∀ k, ‖l k‖ = 1) (hVA : vandermonde l * A = diagonal l * vandermonde l) :
    A.det ≠ 0 ∧ (Matrix.of fun i j : Fin n => trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ))) = (vandermonde l)ᴴ * vandermonde l ∧
      ((vandermonde l)ᴴ * vandermonde l).det ≠ 0 ∧
      Aᴴ * ((vandermonde l)ᴴ * vandermonde l) * A = (vandermonde l)ᴴ * vandermonde l := by
  set V := vandermonde l with hV
  have hl0 : ∀ k, l k ≠ 0 := fun k h => by simpa [h] using h1 k
  have hVd : V.det ≠ 0 := det_vandermonde_ne_zero_iff.2 hl
  have hconj : ∀ k, starRingEnd ℂ (l k) = (l k)⁻¹ := by
    intro k
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1 k]; simp
  have hAd : A.det ≠ 0 := by
    have := congrArg Matrix.det hVA
    rw [det_mul, det_mul, det_diagonal, mul_comm] at this
    have h2 : A.det = ∏ k, l k := mul_right_cancel₀ hVd this
    rw [h2]; exact Finset.prod_ne_zero_iff.2 fun k _ => hl0 k
  set D' := diagonal fun k => (l k)⁻¹
  have hDD : D' * diagonal l = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext k; exact inv_mul_cancel₀ (hl0 k)
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAd)
  have hVAi : V * A⁻¹ = D' * V := by
    calc V * A⁻¹ = D' * diagonal l * V * A⁻¹ := by rw [hDD, one_mul]
      _ = D' * (V * A) * A⁻¹ := by rw [hVA, mul_assoc D']
      _ = D' * V := by rw [mul_assoc, mul_assoc, hAinv, mul_one]
  have hpow : ∀ j : ℕ, V * A ^ j = diagonal l ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVA, ← mul_assoc, ← pow_succ]
  have hpowi : ∀ j : ℕ, V * A⁻¹ ^ j = D' ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVAi, ← mul_assoc, ← pow_succ]
  have hVinv : V⁻¹ * V = 1 := nonsing_inv_mul V (isUnit_iff_ne_zero.2 hVd)
  have hVinv' : V * V⁻¹ = 1 := mul_nonsing_inv V (isUnit_iff_ne_zero.2 hVd)
  refine ⟨hAd, ?_, ?_, ?_⟩
  · ext i j
    have hM : V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V := by
      rw [← mul_assoc, hpowi, mul_assoc, hpow, ← mul_assoc]
    have htr : trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
      calc trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (V⁻¹ * (V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)))) := by
            rw [← mul_assoc, hVinv, one_mul]
        _ = trace (V⁻¹ * ((D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V)) := by rw [hM]
        _ = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
            rw [trace_mul_comm, mul_assoc, hVinv', mul_one]
    rw [of_apply, htr, diagonal_pow, diagonal_pow, diagonal_mul_diagonal, trace_diagonal, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [V, D', vandermonde_apply, conjTranspose_apply, hconj, inv_pow]
  · rw [det_mul, det_conjTranspose]
    exact mul_ne_zero (by simpa using hVd) hVd
  · calc Aᴴ * (Vᴴ * V) * A = (V * A)ᴴ * (V * A) := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * ((diagonal l)ᴴ * diagonal l) * V := by
          rw [hVA, conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * V := by
          rw [diagonal_conjTranspose, diagonal_mul_diagonal]
          have : (diagonal fun k => star (l k) * l k) = 1 := by
            rw [← diagonal_one]; congr 1; funext k
            show starRingEnd ℂ (l k) * l k = 1
            rw [hconj, inv_mul_cancel₀ (hl0 k)]
          simp only [Pi.star_apply] at this ⊢
          rw [this, mul_one]

end GlobalTheory.GlobHerm

namespace GlobalTheory.GlobHerm

theorem exists_mat_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  intro E _ _ _ n P hP
  obtain ⟨hmon, hdeg, hsep, hroot⟩ := hP
  subst hdeg
  have hP0 : P ≠ 0 := hmon.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  let Cm : Matrix (Fin P.natDegree) (Fin P.natDegree) E := Algebra.leftMulMatrix pb.basis pb.gen
  let H : Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
    Matrix.of fun i j => trace (Cm⁻¹ ^ (i : ℕ) * Cm ^ (j : ℕ))
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτc : ∀ x, τ ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = starRingEnd ℂ (τ x) :=
    fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQsep : (P.map τ).Separable := hsep.map
  have hQcard : (P.map τ).roots.card = P.natDegree := by
    rw [splits_iff_card_roots.1 (IsAlgClosed.splits _), natDegree_map]
  have hs : (P.map τ).roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hQsep), hQcard]
  let e : (P.map τ).roots.toFinset ≃ Fin P.natDegree := Fintype.equivFinOfCardEq (by simp [hs])
  let l : Fin P.natDegree → ℂ := fun k => (e.symm k : ℂ)
  have hl : Function.Injective l := Subtype.val_injective.comp e.symm.injective
  have hlr : ∀ k, eval₂ τ (l k) P = 0 := by
    intro k
    have := (e.symm k).2
    rw [Multiset.mem_toFinset, mem_roots hQsep.ne_zero, IsRoot, eval_map] at this
    exact this
  have h1 : ∀ k, ‖l k‖ = 1 := fun k => hroot τ _ (Multiset.mem_toFinset.1 (e.symm k).2)
  have hrep : ∀ k (x : AdjoinRoot P),
      ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (pb.basis.repr x i) = AdjoinRoot.lift τ (l k) (hlr k) x := by
    intro k x
    conv_rhs => rw [← pb.basis.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, PowerBasis.coe_basis]
    simp only [pb, AdjoinRoot.powerBasis_gen, map_pow, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    ring
  have hVA : vandermonde l * Cm.map τ = diagonal l * vandermonde l := by
    ext k j
    rw [Matrix.mul_apply, diagonal_mul, vandermonde_apply]
    show ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (Algebra.leftMulMatrix pb.basis pb.gen i j) = l k * l k ^ (j : ℕ)
    have hC : ∀ i : Fin pb.dim, Algebra.leftMulMatrix pb.basis pb.gen i j = pb.basis.repr (pb.gen * pb.basis j) i :=
      fun i => Algebra.leftMulMatrix_eq_repr_mul _ _ _ _
    rw [Finset.sum_congr rfl fun i _ => by rw [hC i], hrep k]
    simp only [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rw [← pow_succ', map_pow, AdjoinRoot.lift_root, pow_succ']
  obtain ⟨hAd, hH, hHd, hpres⟩ := GlobalTheory.GlobHerm.vandermonde_diag_herm (Cm.map τ) l hl h1 hVA
  have hinv : (Cm.map τ)⁻¹ = Cm⁻¹.map τ := by
    apply inv_eq_left_inv
    have hCd : Cm.det ≠ 0 := by
      intro h; apply hAd
      have := RingHom.map_det τ Cm
      rw [h, map_zero] at this
      exact this.symm
    rw [← Matrix.map_mul, nonsing_inv_mul Cm (isUnit_iff_ne_zero.2 hCd), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hHm : H.map τ = (vandermonde l)ᴴ * vandermonde l := by
    rw [← hH]
    ext i j
    simp only [map_apply, of_apply, H]
    rw [AddMonoidHom.map_trace τ, hinv]
    congr 1
    change τ.mapMatrix _ = _
    rw [map_mul, map_pow, map_pow]
    rfl
  have hinj : Function.Injective (fun M : Matrix (Fin P.natDegree) (Fin P.natDegree) E => M.map τ) :=
    Matrix.map_injective τ.injective
  have hcT : ∀ M : Matrix (Fin P.natDegree) (Fin P.natDegree) E,
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map τ = (M.map τ)ᴴ := by
    intro M; ext i j
    simp only [cT, map_apply, transpose_apply, conjTranspose_apply, hτc]
    rfl
  refine ⟨Cm, H, ?_, ?_, ?_, ?_, ?_⟩
  · refine (charpoly_leftMulMatrix pb).trans ?_
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hmon.leadingCoeff, inv_one,
      Polynomial.C_1, mul_one]
  · intro h; apply hAd
    have := RingHom.map_det τ Cm
    rw [h, map_zero] at this
    exact this.symm
  · intro h; apply hHd
    have := RingHom.map_det τ H
    rw [h, map_zero] at this
    rw [← hHm]; exact this.symm
  · apply hinj
    simp only
    rw [hcT, hHm, conjTranspose_mul, conjTranspose_conjTranspose]
  · apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT, hHm, hpres]
end GlobalTheory.GlobHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeStableOfHeckeFramePolynomialActionStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  first | exact @GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke | exact GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke | (intros; apply GlobalTheory.ExpFrame.heckeStable_heckeNat_of_isHecke <;> assumption)
end

