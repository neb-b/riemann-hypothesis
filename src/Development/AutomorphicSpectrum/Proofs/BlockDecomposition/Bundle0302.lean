module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenRsLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0241

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

abbrev Idx.swap {c n : ℕ} (t : Idx c n) : Idx c n :=
  ⟨t.a', t.j, t.a, t.i, by have := t.ha; omega, by have := t.h; omega⟩

def swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) :
    (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) →ₗ[K]
      (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) :=
  DirectSum.toModule K _ _ fun t =>
    ((-1 : ℤ) ^ (t.i * t.j)) •
      ((DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap).comp
        (TensorProduct.comm K ((P t.a).H t.i) ((Q t.a').H t.j)).toLinearMap)

theorem swapSum_lof (P Q : ℕ → Cx.{w} K) (c n : ℕ) (t : Idx c n) (u : (P t.a).H t.i) (v : (Q t.a').H t.j) :
    swapSum P Q c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t (u ⊗ₜ v)) =
      ((-1 : ℤ) ^ (t.i * t.j)) •
        DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap (v ⊗ₜ u) := by
  unfold swapSum
  rw [DirectSum.toModule_lof]
  rfl

theorem swapSum_swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) (z) :
    swapSum Q P c n (swapSum P Q c n z) = z := by
  have key : (swapSum Q P c n).comp (swapSum P Q c n) = LinearMap.id := by
    refine DirectSum.linearMap_ext K fun t => TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, swapSum_lof, map_zsmul]
    have hs : ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.swap.i * t.swap.j)) = 1 := by
      change ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.j * t.i)) = 1
      rw [Nat.mul_comm t.j t.i, ← mul_pow]
      simp
    refine (congrArg (fun w => ((-1 : ℤ) ^ (t.i * t.j)) • w) (swapSum_lof Q P c n t.swap v u)).trans ?_
    dsimp only
    rw [smul_smul, hs, one_smul]
  exact LinearMap.congr_fun key z

theorem kunE_swap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (h : KunE pr) :
    KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  intro c n
  obtain ⟨e, he⟩ := h c n
  let σ : (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) ≃ₗ[K]
      (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) :=
    LinearEquiv.ofLinear (swapSum Q P c n) (swapSum P Q c n)
      (LinearMap.ext fun z => swapSum_swapSum P Q c n z) (LinearMap.ext fun z => swapSum_swapSum Q P c n z)
  refine ⟨σ.trans e, fun t x y hx hy hz => ?_⟩
  have hz' : (T c).d n ((pr (show t.a' + t.a = c by have := t.ha; omega)).μ (show t.j + t.i = n by have := t.h; omega) y x) = 0 := by
    have e0 := (pr (show t.a' + t.a = c by have := t.ha; omega)).leib (show t.j + t.i = n by have := t.h; omega) y x
    rw [e0, hx, hy]
    simp
  have e1 := he t.swap y x hy hx hz'
  change e (swapSum Q P c n (DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t
    ((Q t.a).cls x hx ⊗ₜ (P t.a').cls y hy))) = _
  rw [swapSum_lof]
  change e.toLinearMap (((-1 : ℤ) ^ (t.i * t.j)) •
    DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t.swap
      ((P t.a').cls y hy ⊗ₜ (Q t.a).cls x hx)) = _
  rw [map_zsmul e.toLinearMap]
  refine (congrArg _ e1).trans ?_
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamFamily
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Fam
variable {K : Type} [CommRing K] {ι : Type} {a : ℕ}

theorem lam_family (hDW : DWedge) (hDL : DLog) (hFL : FormLaws) (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    {H₂ X₂ H₃ X₃ : Finset ι → Type*} [∀ S, AddCommGroup (H₂ S)] [∀ S, Module K (H₂ S)]
    [∀ S, AddCommGroup (X₂ S)] [∀ S, Module K (X₂ S)] [∀ S, AddCommGroup (H₃ S)] [∀ S, Module K (H₃ S)]
    [∀ S, AddCommGroup (X₃ S)] [∀ S, Module K (X₃ S)]
    (i₂ : ∀ S, H₂ S →ₗ[K] X₂ S) (i₃ : ∀ S, H₃ S →ₗ[K] X₃ S)
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] X₂ S)) (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] X₃ S))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS)) (hi₃ : ∀ S, S.Nonempty → Function.Injective (i₃ S))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range (i₂ S) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range (i₃ S) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (ρ₂ : ∀ {S T : Finset ι}, S ⊆ T → (H₂ S →ₗ[K] H₂ T)) (ρ₃ : ∀ {S T : Finset ι}, S ⊆ T → (H₃ S →ₗ[K] H₃ T))
    (x₂ : ∀ {S T : Finset ι}, S ⊆ T → (X₂ S →ₗ[K] X₂ T)) (x₃ : ∀ {S T : Finset ι}, S ⊆ T → (X₃ S →ₗ[K] X₃ T))
    (hρ₂ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₂ T (ρ₂ h y) = x₂ h (i₂ S y))
    (hρ₃ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₃ T (ρ₃ h y) = x₃ h (i₃ S y))
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₂ h (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₃ h (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω)) :
    ∃ lam : ∀ (α : ι) (S : Finset ι), α ∈ S → (H₂ S →ₗ[K] H₃ S),
      (∀ α {S T : Finset ι} (h : S ⊆ T) hS y, lam α T (h hS) (ρ₂ h y) = ρ₃ h (lam α S hS y)) ∧
      ∀ α S hα y ω η (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
        (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (f α S hα) g)) →
        i₂ S y = e₂ S ⟨α, hα⟩ ω → f α S hα • η = w ω → i₃ S (lam α S hα y) = e₃ S ⟨α, hα⟩ (c • η) := by
  have key := fun (α : ι) (S : Finset ι) (hα : α ∈ S) =>
    lam_one hDW hDL hFL (i₂ S) (i₃ S) (e₂ S ⟨α, hα⟩) (e₃ S ⟨α, hα⟩) (he₂ S _) (hi₃ S ⟨α, hα⟩) (I S) (hr₂ S _)
      (hr₃ S _) (f α S hα) (hI α S hα) (hnz α S hα) c
  choose lam hlam using key
  refine ⟨lam, fun α S T h hα y => ?_, hlam⟩
  have hS : S.Nonempty := ⟨α, hα⟩
  have hT : T.Nonempty := ⟨α, h hα⟩
  refine hi₃ T hT ?_
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 (i₂ S y)
  have hm : ω ∈ relOm K (Ideal.span {f α S hα}) a := by
    rw [← hI α S hα]
    exact (hr₂ S hS ω).1 ⟨y, hω.symm⟩
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm
  obtain ⟨w', hw'⟩ := hDW K (A T) a (f α T (h hα))
  have wm := wedge_map hFL (φ h) (f α S hα) w w' hw (by rw [hφ]; exact hw') ω
  have s1 := hlam α S hα y ω η w hw hω.symm hη
  have s2 := hlam α T (h hα) (ρ₂ h y) (omMap (φ h) a ω) (omMap (φ h) (a + 1) η) w' hw'
    (by rw [hρ₂, ← hω, hx₂ h hS hT]) (by
      rw [← wm, ← hη, ((hFL K (A S) (A T) (a + 1)).2 (φ h)).2.1, hφ])
  rw [s2, hρ₃, s1, hx₃ h hS hT, map_zsmul (omMap (φ h) (a + 1))]

end Fam

section Kill
variable {K : Type} [CommRing K] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} K} {ι : Type} [DecidableEq ι]

theorem cov_kill (hCK : ConeKill) (hCD : CovDesc) (hDW : DWedge) (hDL : DLog) (hFL : FormLaws)
    (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C)
    (hU : ∀ α, Cosieve (U α)) {Q : ObjectProperty C} (hQ : Cosieve Q) (a : ℕ)
    (h1 : (covSy F₂ U hQ).One a) (h2 : (covSy F₃ U hQ).One (a + 1))
    (r : CH.Cn F₁ 2) (hr : CH.d F₁ 2 r = 0) (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1)
    (hβ : ∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict F₁ (U α).ι).pullC 2 r)
    (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] HU F₂ (capU U S) a))
    (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] HU F₃ (capU U S) (a + 1)))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS))
    (hi₃ : ∀ S, S.Nonempty → Function.Injective ((incl F₃ (capU U S) hQ).mapH (a + 1)))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range ((incl F₂ (capU U S) hQ).mapH a) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range ((incl F₃ (capU U S) hQ).mapH (a + 1)) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (k : ∀ {S T : Finset ι}, S ⊆ T → capU U T ≤ capU U S)
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₂ (k h)).pull a (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₃ (k h)).pull (a + 1) (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω))
    (u : ∀ (α α' : ι) (S : Finset ι), α ∈ S → α' ∈ S → (A S)ˣ)
    (huf : ∀ α α' S hα hα', f α S hα = u α α' S hα hα' * f α' S hα')
    (hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU U S).ι ⋙ F₂) a) (hy : CH.d _ a y = 0) (ω : Om K (A S) a)
      (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
      (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (u α α' S hα hα' : A S) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU U S).ι ⋙ F₃)).cls ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ (c • ((↑(u α α' S hα hα')⁻¹ : A S) • w ω)))
    (n : ℕ) (x : ((covSy F₂ U hQ).K ∅).X n) (hx : ((covSy F₂ U hQ).K ∅).d n x = 0) :
    rhoS P U hQ r ∅ n x ∈ ((covSy F₃ U hQ).K ∅).B (n + 2) := by
  obtain ⟨lam, lam_nat, lam_spec⟩ := lam_family (K := K) (a := a) hDW hDL hFL A
    (H₂ := fun S => ((covSy F₂ U hQ).K S).H a) (X₂ := fun S => HU F₂ (capU U S) a)
    (H₃ := fun S => ((covSy F₃ U hQ).K S).H (a + 1)) (X₃ := fun S => HU F₃ (capU U S) (a + 1))
    (fun S => (incl F₂ (capU U S) hQ).mapH a) (fun S => (incl F₃ (capU U S) hQ).mapH (a + 1))
    e₂ e₃ he₂ hi₃ I hr₂ hr₃ f hI hnz c φ hφ
    (fun h => ((covSy F₂ U hQ).res h).mapH a) (fun h => ((covSy F₃ U hQ).res h).mapH (a + 1))
    (fun h => (resU F₂ (k h)).pull a) (fun h => (resU F₃ (k h)).pull (a + 1))
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    hx₂ hx₃
  refine cone_apply hCK hCD P U hU hQ a h1 h2 r hr β hβ lam (fun α S T h hS x => lam_nat α h hS x) ?_ n x hx
  intro α α' S hα hα' x hx hz
  have hS : S.Nonempty := ⟨α, hα⟩
  refine hi₃ S hS ?_
  have hy : CH.d _ a x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 ((CH.cx _).cls x.1 hy)
  have hi : (incl F₂ (capU U S) hQ).mapH a (((covSy F₂ U hQ).K S).cls x hx) = e₂ S hS ω := hω.symm
  have hm : ω ∈ relOm K (I S) a := (hr₂ S hS ω).1 ⟨_, hi⟩
  have hm₁ : ω ∈ relOm K (Ideal.span {f α S hα}) a := hI α S hα ▸ hm
  have hm₂ : ω ∈ relOm K (Ideal.span {f α' S hα'}) a := hI α' S hα' ▸ hm
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨w', hw'⟩ := hDW K (A S) a (f α' S hα')
  obtain ⟨wu, hwu⟩ := hDW K (A S) a (u α α' S hα hα' : A S)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm₁
  obtain ⟨η', ⟨-, hη'⟩, -⟩ := hDL K (A S) a (f α' S hα') (hnz α' S hα') w' hw' ω hm₂
  have d := eta_diff hFL (u α α' S hα hα') (f α S hα) (f α' S hα') (huf α α' S hα hα') (hnz α S hα) w w' wu hw hw' hwu
    ω η η' hη hη'
  have s1 := lam_spec α S hα _ ω η w hw hi hη
  have s2 := lam_spec α' S hα' _ ω η' w' hw' hi hη'
  have hz' : CH.d ((capU U S).ι ⋙ F₃) (a + 1) ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
      ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    exact congrArg Subtype.val hz
  have s3 := hcup α α' S hα hα' x.1 hy ω wu hwu hω.symm hz'
  have e1 : (incl F₃ (capU U S) hQ).mapH (a + 1) (((covSy F₃ U hQ).K S).cls
      (etaS P U hQ β α S hα a x - etaS P U hQ β α' S hα' a x) hz) = (CH.cx ((capU U S).ι ⋙ F₃)).cls
      ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) hz' := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (LinearMap.congr_fun (map_sub ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)) _ _) x.1).symm
  have e2 := (map_sub ((incl F₃ (capU U S) hQ).mapH (a + 1)) (lam α S hα (((covSy F₂ U hQ).K S).cls x hx))
    (lam α' S hα' (((covSy F₂ U hQ).K S).cls x hx))).trans (congrArg₂ (· - ·) s1 s2)
  refine (e1.trans s3).trans (Eq.trans ?_ e2.symm)
  have e3 : (e₃ S ⟨α', hα'⟩ : _) = e₃ S ⟨α, hα⟩ := rfl
  rw [e3, ← map_sub, ← smul_sub, d]

end Kill

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEquivContinuous
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviCont

theorem levi_iso_homeo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) : Continuous φ ∧ Continuous φ.symm := by
  have hcont : ∀ (Ψ : Levi k m → GL (Fin N) k) (ρ : ∀ a, GL (m a) k → Matrix (m a) (m a) k),
      (∀ a, Continuous (ρ a)) →
      (∀ g a (i j : m a), (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) = ρ a (g a) i j) →
      (∀ g a b (i : m a) (j : m b), a ≠ b →
        (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0) →
      Continuous fun g => (Ψ g : Matrix (Fin N) (Fin N) k) := by
    intro Ψ ρ hρ hs hn
    refine continuous_pi fun r => continuous_pi fun s => ?_
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective r
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective s
    by_cases hab : a = b
    · subst hab
      simp_rw [hs]
      exact (continuous_apply j).comp ((continuous_apply i).comp ((hρ a).comp (continuous_apply a)))
    · simp_rw [hn _ _ _ _ _ hab]
      exact continuous_const
  have hinv : ∀ g, ((φ g : levi k N β) : GL (Fin N) k)⁻¹ = leviEmb k e g⁻¹ := by
    intro g
    rw [← hφ, map_inv, Subgroup.coe_inv]
  have hs1 : ∀ g a (i j : m a), ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (g a : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hφ]
    exact leviEmb_apply_same k e g a i j
  have hs2 : ∀ g a (i j : m a),
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (((g a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hinv]
    exact leviEmb_apply_same k e g⁻¹ a i j
  have hn1 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hφ]
    exact leviEmb_apply_ne k e g hab i j
  have hn2 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hinv]
    exact leviEmb_apply_ne k e g⁻¹ hab i j
  refine ⟨?_, ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact hcont (fun g => (φ g : GL (Fin N) k)) (fun a u => (u : Matrix (m a) (m a) k))
        (fun a => Units.continuous_val) hs1 hn1
    · exact hcont (fun g => ((φ g : GL (Fin N) k))⁻¹) (fun a u => ((u⁻¹ : GL (m a) k) : Matrix (m a) (m a) k))
        (fun a => Units.continuous_coe_inv) hs2 hn2
  · refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, ((φ.symm h a : GL (m a) k) : Matrix (m a) (m a) k) i j =
          ((h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs1, MulEquiv.apply_symm_apply]
      simp_rw [Function.comp_apply, h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, (((φ.symm h a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j =
          (((h : GL (Fin N) k))⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs2, MulEquiv.apply_symm_apply]
      simp_rw [h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_coe_inv (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))

end GlobalTheory.CompanionTheory.LeviCont
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRefinementParabolic
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.RelUnipBridge

theorem one_apply_sigma {k n α : Type} [Zero k] [One k] [DecidableEq n] {m : α → Type}
    [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (a : α) (r s : m a) :
    (1 : Matrix n n k) (e ⟨a, r⟩) (e ⟨a, s⟩) = (1 : Matrix (m a) (m a) k) r s := by
  by_cases h : r = s
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    intro h'
    have := e.injective h'
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact h this

theorem mem_relUnip_iff_leviEmb_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m), x ∈ relUnip k f ↔ leviEmb k e x ∈ unipotentRadical k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical]
  constructor
  · intro hx
    have hx' : ∀ a, x a ∈ unipRad k (f a) := fun a => hx a trivial
    refine ⟨fun r s hrs => ?_, fun r s hrs => ?_⟩
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        exact mem_parab_iff.1 (mem_unipRad.1 (hx' a)).1 j j' t t' ((hδ a j' j t' t).1 hrs)
      · exact leviEmb_apply_ne k e x hab r s
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, one_apply_sigma]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        have hjj : j = j' := by
          rcases lt_trichotomy j j' with h | h | h
          · exact absurd ((hδ a j j' t t').2 h) hrs.not_lt
          · exact h
          · exact absurd ((hδ a j' j t' t).2 h) hrs.symm.not_lt
        subst hjj
        rw [one_apply_sigma]
        exact (mem_unipRad.1 (hx' a)).2 j t t'
      · rw [leviEmb_apply_ne k e x hab r s, Matrix.one_apply_ne]
        intro h
        exact hab (congrArg Sigma.fst (e.injective h))
  · rintro ⟨hP, h1⟩ a -
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun j j' t t' hjj => ?_, fun j t t' => ?_⟩
    · have := hP ((hδ a j' j t' t).2 hjj)
      rwa [leviEmb_apply_same] at this
    · have hd : δ (e ⟨a, f a ⟨j, t⟩⟩) = δ (e ⟨a, f a ⟨j, t'⟩⟩) := by
        rcases lt_trichotomy (δ (e ⟨a, f a ⟨j, t⟩⟩)) (δ (e ⟨a, f a ⟨j, t'⟩⟩)) with h | h | h
        · exact absurd ((hδ a j j t t').1 h) (lt_irrefl j)
        · exact h
        · exact absurd ((hδ a j j t' t).1 h) (lt_irrefl j)
      have := h1 _ _ hd
      rwa [leviEmb_apply_same, one_apply_sigma, one_apply_sigma] at this

end GlobalTheory.CompanionTheory.RelUnipBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompat
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section CoefIdeal
variable {X : Scheme.{0}} {V V' : X.Opens} (h : V ≤ V') {d m : ℕ}
  (D : Fin d → Γ(X, V) → Γ(X, V)) (κ : Fin m → Fin d)

theorem rs_mul_mem_jacSpan (b : Γ(X, V')) {y : Γ(X, V)} (hy : y ∈ jacSpan h (RingHom.id _) D κ) :
    rs h b * y ∈ jacSpan h (RingHom.id _) D κ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b', bs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨b * b', bs, ?_⟩
    simp only [RingHom.id_apply, map_mul, mul_assoc]
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [mul_neg]; exact neg_mem h1

def coefIdeal (y : Γ(X, V)) : Ideal Γ(X, V') where
  carrier := {a | rs h a * y ∈ jacSpan h (RingHom.id _) D κ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add (f := _), add_mul]
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, zero_mul]
    exact zero_mem _
  smul_mem' b a ha := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
    rw [map_mul, mul_assoc]
    exact rs_mul_mem_jacSpan h D κ b ha

theorem mem_coefIdeal {y : Γ(X, V)} {a : Γ(X, V')} :
    a ∈ coefIdeal h D κ y ↔ rs h a * y ∈ jacSpan h (RingHom.id _) D κ := Iff.rfl

theorem ideal_eq_top_of_local {U : X.Opens} (hU : IsAffineOpen U) (𝔠 : Ideal Γ(X, U))
    (H : ∀ x : X, x ∈ U → ∃ (f : Γ(X, U)) (M : ℕ), x ∈ X.basicOpen f ∧ f ^ M ∈ 𝔠) : 𝔠 = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔠 hne
  have hPp : P.IsPrime := hP.isPrime
  let p : PrimeSpectrum Γ(X, U) := ⟨P, hPp⟩
  have hxU : hU.fromSpec p ∈ U := by
    have : hU.fromSpec p ∈ Set.range hU.fromSpec := ⟨p, rfl⟩
    rwa [hU.range_fromSpec] at this
  obtain ⟨f, M, hx, hf⟩ := H _ hxU
  have hfP : f ∈ P := hPp.mem_of_pow_mem M (hle hf)
  have e : hU.fromSpec p ∈ X.basicOpen f := hx
  have e2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := e
  rw [hU.fromSpec_preimage_basicOpen] at e2
  exact e2 hfP

end CoefIdeal

theorem coef_mem_jacSpan : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  intro K _ _ X q _ s V V' hVV hV' d c
  intro D hD E ε hL σ m r hr hs ξ y hRep I
  have top : coefIdeal hVV (fun k => D k) I.1 (y I) = ⊤ := by
    refine ideal_eq_top_of_local hV' _ fun x hx => ?_
    obtain ⟨f, e, cu, hxf⟩ := GlobalTheory.CompanionTheory.ConeLocal.coord_near q hV' x hx
    obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ConeLocal.CoefMemLoc.main q s hVV hV' c D hD E ε hL σ m r hr hs f e cu ξ y hRep I
    exact ⟨f, M, hxf, hM⟩
  have h1 : (1 : Γ(X, V')) ∈ coefIdeal hVV (fun k => D k) I.1 (y I) := top ▸ Submodule.mem_top
  have h2 := (mem_coefIdeal hVV _ _).1 h1
  rwa [map_one, one_mul] at h2

end GlobalTheory.CompanionTheory.ConeLocal
end
end

