module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}

abbrev sumN (M : ℕ → X.Modules) (k d e : ℕ) : X.Modules := ⨁ fun _ : Fin k => M (d + e)

def sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : sumN M k d e ⟶ M (d + e + 1) :=
  biproduct.desc fun i => T i (d + e)

def diagOp (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    sumN M k d e ⟶ sumN M k d (e + 1) :=
  biproduct.map fun _ => T j (d + e)

abbrev kerSeq (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : X.Modules := kernel (sumMap T d e)

theorem diagOp_sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    diagOp T d j e ≫ sumMap T d (e + 1) = sumMap T d e ≫ T j (d + e + 1) := by
  apply biproduct.hom_ext'
  intro i
  simp only [diagOp, sumMap, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
  exact hc j i (d + e)

def kerOp (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerSeq T d e ⟶ kerSeq T d (e + 1) :=
  kernel.lift _ (kernel.ι _ ≫ diagOp T d j e) (by
    rw [Category.assoc, diagOp_sumMap T hc, kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem kerOp_ι (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerOp T hc d j e ≫ kernel.ι _ = kernel.ι _ ≫ diagOp T d j e :=
  kernel.lift_ι _ _ _

theorem diagOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    diagOp T d i e ≫ diagOp T d j (e + 1) = diagOp T d j e ≫ diagOp T d i (e + 1) := by
  apply biproduct.hom_ext
  intro l
  simp only [diagOp, Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  exact biproduct.π _ l ≫= hc i j (d + e)

theorem kerOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    kerOp T hc d i e ≫ kerOp T hc d j (e + 1) = kerOp T hc d j e ≫ kerOp T hc d i (e + 1) := by
  rw [← cancel_mono (kernel.ι _)]
  simp only [Category.assoc, kerOp_ι, kerOp_ι_assoc]
  rw [diagOp_comm T hc]

def kerSC (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (sumMap T d e)) (sumMap T d e) (kernel.condition _)

theorem kerSC_shortExact (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) [Epi (sumMap T d e)] :
    (kerSC T d e).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (inferInstanceAs (Mono (kernel.ι (sumMap T d e))))
    (inferInstanceAs (Epi (sumMap T d e)))

end GlobalTheory.CompanionTheory.GE.KerSeq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmooth
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

variable {K : Type} [Field K]

def topResEquiv (hT : TopRes) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (hU : ∀ T, U T) (n : ℕ) : CH.H F n ≃ₗ[K] CH.H (U.ι ⋙ F) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F U.ι).pull n)
    (CrystallineSemistableComparison.P.mapH_bij (CH.Mor.restrict F U.ι).hom (fun m => (hT K C F U ⊥ hU m).1) n)

theorem cls_congr' {R : Type} [CommRing R] {L : Cx.{1} R} {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0)
    (hy : L.d n y = 0) : L.cls x hx = L.cls y hy := by
  subst e
  rfl

theorem XD.pr_restrict (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c p q n : ℕ} (ha : a + a' = c)
    (h : p + q = n) (x : CH.Cn (E.F₁ a) p) (y : CH.Cn (E.F₂ a') q) :
    (E.pr U₁ U₂ U₃ h₁ h₂ ha).μ h ((CH.Mor.restrict (E.F₁ a) U₁.ι).pullC p x)
        ((CH.Mor.restrict (E.F₂ a') U₂.ι).pullC q y) =
      (CH.Mor.restrict (E.F₃ c) U₃.ι).pullC n
        ((E.μ ha).cupC h ((E.m₁ a).pullC p x) ((E.m₂ a').pullC q y)) := by
  funext s
  rfl

theorem XD.kun_cup (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {c n : ℕ}
    (e : (⨁ t : Idx c n, (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) ≃ₗ[K]
      (CH.cx (U₃.ι ⋙ E.F₃ c)).H n)
    (he : ∀ (t : Idx c n) (x : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).X t.i) (y : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).X t.j)
      (hx : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).d t.i x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).d t.j y = 0)
      (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        ((CH.cx (U₁.ι ⋙ E.F₁ t.a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ t.a')).cls y hy)) =
        (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) hz)
    (t : Idx c n) (u : CH.H (E.F₁ t.a) t.i) (v : CH.H (E.F₂ t.a') t.j) :
    topResEquiv hT (E.F₃ c) U₃ hU₃ n
        ((E.μ t.ha).cup t.h ((E.m₁ t.a).pull t.i u) ((E.m₂ t.a').pull t.j v)) =
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        (topResEquiv hT (E.F₁ t.a) U₁ hU₁ t.i u ⊗ₜ topResEquiv hT (E.F₂ t.a') U₂ hU₂ t.j v)) := by
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj u
  obtain ⟨y, hy, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj v
  have hx₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₁ t.a).hom x hx
  have hy₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₂ t.a').hom y hy
  obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (E.μ t.ha) t.h _ _ hx₁ hy₁
  have hx₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₁ t.a) U₁.ι).hom x hx
  have hy₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₂ t.a') U₂.ι).hom y hy
  have hc₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₃ c) U₃.ι).hom _ hc
  have hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h
      ((CH.Mor.restrict (E.F₁ t.a) U₁.ι).pullC t.i x) ((CH.Mor.restrict (E.F₂ t.a') U₂.ι).pullC t.j y)) = 0 := by
    rw [XD.pr_restrict]
    exact hc₂
  have key := he t _ _ hx₂ hy₂ hz
  refine Eq.trans ?_ key.symm |>.trans rfl
  change (CH.Mor.restrict (E.F₃ c) U₃.ι).pull n ((E.μ t.ha).cup t.h ((CH.cx _).cls _ hx₁) ((CH.cx _).cls _ hy₁)) = _
  rw [ec]
  exact cls_congr' (XD.pr_restrict E U₁ U₂ U₃ h₁ h₂ t.ha t.h x y).symm hc₂ hz

def sliceMap {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) :
    A ⊗[K] B →ₗ[K] B₀ :=
  (TensorProduct.lid K B₀).toLinearMap ∘ₗ TensorProduct.map (φ ∘ₗ r₁.symm.toLinearMap) r₂.symm.toLinearMap

theorem sliceMap_tmul {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) (u : A₀) (v : B₀) :
    sliceMap r₁ r₂ φ (r₁ u ⊗ₜ r₂ v) = φ u • v := by
  simp [sliceMap]

def compMap {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) : A →ₗ[K] W :=
  g ∘ₗ DirectSum.component K ι N t₀ ∘ₗ e.symm.toLinearMap ∘ₗ ρ.toLinearMap

theorem compMap_self {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (w : N t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t₀ w)) : compMap N ρ e t₀ g x = g w := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.lof_self]

theorem compMap_ne {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (t : ι) (w : N t) (ht : t ≠ t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t w)) : compMap N ρ e t₀ g x = 0 := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.of, dite_eq_right ht, map_zero]

theorem XD.slant (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (hK : E.Kun U₁ U₂ U₃ h₁ h₂)
    (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (CH.H (E.F₁ a) i)) :
    ∃ sl : CH.H (E.F₃ c) n →ₗ[K] CH.H (E.F₂ a') j,
      (∀ u v, sl ((E.μ ha).cup h ((E.m₁ a).pull i u) ((E.m₂ a').pull j v)) = φ u • v) ∧
      ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) →
        ∀ (u : CH.H (E.F₁ b) i') (v : CH.H (E.F₂ b') j'),
          sl ((E.μ hb).cup h' ((E.m₁ b).pull i' u) ((E.m₂ b').pull j' v)) = 0 := by
  obtain ⟨e, he⟩ := hK c n
  have kc := XD.kun_cup hT E U₁ U₂ U₃ hU₁ hU₂ hU₃ h₁ h₂ e he
  refine ⟨compMap (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j)
    (topResEquiv hT (E.F₃ c) U₃ hU₃ n) e ⟨a, i, a', j, ha, h⟩
    (sliceMap (topResEquiv hT (E.F₁ a) U₁ hU₁ i) (topResEquiv hT (E.F₂ a') U₂ hU₂ j) φ), ?_, ?_⟩
  · intro u v
    exact (compMap_self _ _ e _ _ _ _ (kc ⟨a, i, a', j, ha, h⟩ u v)).trans (sliceMap_tmul _ _ φ u v)
  · intro b i' b' j' hb h' hne u v
    refine compMap_ne _ _ e _ _ _ ⟨b, i', b', j', hb, h'⟩ _ ?_ (kc ⟨b, i', b', j', hb, h'⟩ u v)
    intro hh
    exact hne (by rw [show b = a from congrArg Idx.a hh, show i' = i from congrArg Idx.i hh])

theorem slant_of_kun : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  intro hT hS hK K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP a i a' j c n ha h φ
  have top₁ : ∀ T, inU q ⊤ T := fun T => (hS K X X X q (𝟙 X) (𝟙 X)).2.2.1 T
  have top₂ : ∀ T, inU q' ⊤ T := fun T => (hS K X' X' X' q' (𝟙 X') (𝟙 X')).2.2.1 T
  have topP : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    have e : p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ = ⊤ := by simp
    rw [e]
    exact fun T => (hS K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)).2.2.1 T
  have h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T) :=
    fun T _ => top₁ _
  have h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T) :=
    fun T _ => top₂ _
  exact XD.slant hT (hodgeXD q q' p₁ p₂ hP.w.symm) (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤))
    top₁ top₂ topP h₁ h₂ (hK K X X' P q q' p₁ p₂ hP h₁ h₂) a i a' j c n ha h φ

end GlobalTheory.CompanionTheory.KunGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoords
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Aff

universe u w

section Algebra

variable {R : Type} [CommRing R]

theorem tensor_sub_left (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) := by
  have key : ∀ z : M ⊗[R] N, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem tensor_sub_right (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  _root_.UpperTheory.Reformulated.B.Qn17.tensor_sub_right M N

variable {I A : Type} [DecidableEq I] [Fintype A] [DecidableEq A] (M : I → Type u) [∀ t, AddCommMonoid (M t)]
  [∀ t, Module R (M t)] (ι : A → I)

theorem component_lof_ne {i j : I} (h : j ≠ i) (x : M i) : DirectSum.component R I M j (DirectSum.lof R I M i x) = 0 := by
  rw [DirectSum.component.of]
  simp [h.symm]

def sumPi (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) :
    (⨁ t, M t) ≃ₗ[R] ∀ a, M (ι a) :=
  LinearEquiv.ofLinear (LinearMap.pi fun a => DirectSum.component R I M (ι a))
    (∑ a, (DirectSum.lof R I M (ι a)).comp (LinearMap.proj a))
    (by
      refine LinearMap.ext fun f => funext fun b => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply, map_sum]
      rw [Finset.sum_eq_single b]
      · exact DirectSum.component.lof_self R _ _
      · intro a _ hab
        exact component_lof_ne M (fun e => hab (hι e).symm) _
      · intro h
        exact absurd (Finset.mem_univ b) h)
    (by
      refine DirectSum.linearMap_ext R fun t => LinearMap.ext fun x => ?_
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨b, rfl⟩ := ht
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply]
        rw [Finset.sum_eq_single b]
        · rw [DirectSum.component.lof_self]
        · intro a _ hab
          rw [component_lof_ne M (fun e => hab (hι e)) x, map_zero]
        · intro h
          exact absurd (Finset.mem_univ b) h
      · have := hz t ht
        rw [Subsingleton.elim x 0, map_zero, map_zero])

theorem sumPi_lof (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) (b : A) (x : M (ι b)) :
    sumPi (R := R) M ι hι hz (DirectSum.lof R I M (ι b) x) = Pi.single b x := by
  refine funext fun a => ?_
  change DirectSum.component R I M (ι a) (DirectSum.lof R I M (ι b) x) = _
  by_cases h : a = b
  · subst h
    rw [DirectSum.component.lof_self, Pi.single_eq_same]
  · rw [component_lof_ne M (fun e => h (hι e)) x, Pi.single_eq_of_ne h]

end Algebra

variable {K : Type} [Field K]

def diag (c : ℕ) (a : Fin (c + 1)) : Idx c c :=
  ⟨a, a, c - a, c - a, by omega, by omega⟩

theorem diag_inj (c : ℕ) : Function.Injective (diag c) := by
  intro a b h
  exact Fin.ext (congrArg Idx.a h)

theorem kunE_of_diag {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c))
    (hP : ∀ a j, j ≠ a → Subsingleton ((P a).H j)) (hQ : ∀ a j, j ≠ a → Subsingleton ((Q a).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((T a).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((P a).H a) ((Q (c - a)).H (c - a))) ≃ₗ[K] (T c).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (P a).X a) (y : (Q (c - a)).X (c - a))
        (hx : (P a).d a x = 0) (hy : (Q (c - a)).d (c - a) y = 0) (hz : (T c).d c ((pr hc).μ hc x y) = 0),
        e (Pi.single a ((P a).cls x hx ⊗ₜ (Q (c - a)).cls y hy)) = (T c).cls ((pr hc).μ hc x y) hz) :
    KunE pr := by
  intro c n
  have offL : ∀ t : Idx c n, t.i ≠ t.a → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hP t.a t.i h
    exact tensor_sub_left _ _
  have offR : ∀ t : Idx c n, t.j ≠ t.a' → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hQ t.a' t.j h
    exact tensor_sub_right _ _
  by_cases hn : n = c
  · subst hn
    obtain ⟨e, he⟩ := hE n
    have hz : ∀ t, t ∉ Set.range (diag n) → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t ht => by
      refine offL t fun hi => ht ?_
      obtain ⟨a, i, a', j, ha, h⟩ := t
      simp only at hi
      subst hi
      obtain rfl : j = a' := by omega
      obtain rfl : j = n - i := by omega
      exact ⟨⟨i, by omega⟩, rfl⟩
    refine ⟨(sumPi (R := K) (fun t : Idx n n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) (diag n) (diag_inj n) hz).trans e, ?_⟩
    intro t x y hx hy hw
    by_cases ht : t ∈ Set.range (diag n)
    · obtain ⟨b, rfl⟩ := ht
      rw [LinearEquiv.trans_apply, sumPi_lof]
      exact he b (by omega) x y hx hy hw
    · have := hz t ht
      have hi : t.i ≠ t.a := fun hi => ht (by
        obtain ⟨a, i, a', j, ha, h⟩ := t
        simp only at hi
        subst hi
        obtain rfl : j = a' := by omega
        obtain rfl : j = n - i := by omega
        exact ⟨⟨i, by omega⟩, rfl⟩)
      have hB : x ∈ (P t.a).B t.i := by
        have := hP t.a t.i hi
        exact ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 x hx).1 (Subsingleton.elim _ _)
      set_option synthInstance.maxHeartbeats 200000 in
        rw [Subsingleton.elim ((P t.a).cls x hx ⊗ₜ[K] (Q t.a').cls y hy) 0, map_zero, map_zero]
      exact (((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hw).2 (CrystallineSemistableComparison.Auxff.memB_left (pr t.ha) t.h x hB y hy)).symm
  · have : Subsingleton ((T c).H n) := hT c n hn
    have hs : ∀ t : Idx c n, Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t => by
      by_cases hi : t.i = t.a
      · refine offR t fun hj => hn ?_
        have := t.ha
        have := t.h
        omega
      · exact offL t hi
    have : Subsingleton (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) := inferInstance
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem xd_kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (hP : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₁.ι ⋙ E.F₁ a)).H j))
    (hQ : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₂.ι ⋙ E.F₂ a)).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₃.ι ⋙ E.F₃ a)).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((CH.cx (U₁.ι ⋙ E.F₁ a)).H a) ((CH.cx (U₂.ι ⋙ E.F₂ (c - a))).H (c - a))) ≃ₗ[K] (CH.cx (U₃.ι ⋙ E.F₃ c)).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (CH.cx (U₁.ι ⋙ E.F₁ a)).X a) (y : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).X (c - a))
        (hx : (CH.cx (U₁.ι ⋙ E.F₁ a)).d a x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).d (c - a) y = 0)
        (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d c ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) = 0),
        e (Pi.single a ((CH.cx (U₁.ι ⋙ E.F₁ a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).cls y hy)) =
          (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) hz) :
    E.Kun U₁ U₂ U₃ h₁ h₂ :=
  kunE_of_diag (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) hP hQ hT hE

theorem cls_eq {R : Type} [CommRing R] (L : Cx.{w} R) {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0) (hy : L.d n y = 0) :
    L.cls x hx = L.cls y hy := by
  subst e
  rfl

section
variable {X X' P : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q)

theorem hodge_pr_eq (U₁ : ObjectProperty (Thick (smFun X q))) (U₂ : ObjectProperty (Thick (smFun X' q')))
    (U₃ : ObjectProperty (Thick (smFun P (p₁ ≫ q))))
    (h₁ : ∀ T, U₃ T → U₁ ((smS p₁ rfl).G.obj T)) (h₂ : ∀ T, U₃ T → U₂ ((smS p₂ hw).G.obj T)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) (x : CH.Cn (U₁.ι ⋙ G q a) i) (y : CH.Cn (U₂.ι ⋙ G q' a') j) :
    ((hodgeXD q q' p₁ p₂ hw).pr U₁ U₂ U₃ h₁ h₂ ha).μ h x y =
      cupU (p₁ ≫ q) U₃ ha h ((morV p₁ rfl a h₁).pullC i x) ((morV p₂ hw a' h₂).pullC j y) := rfl

end


set_option maxHeartbeats 400000 in
theorem kun_aff : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂  := by
  intro _ hA hK K _ _ X X' P q q' p₁ p₂ hP V V' d d' hc hc' h₁ h₂
  obtain ⟨hZ, hE⟩ := hK K X X' P q q' p₁ p₂ hP V V' d d' hc hc'
  refine xd_kun (hodgeXD q q' p₁ p₂ hP.w.symm) _ _ _ h₁ h₂ ?_ ?_ ?_ ?_
  · exact fun a j hj => (hA K X q V d hc a).1 j hj
  · exact fun a j hj => (hA K X' q' V' d' hc' a).1 j hj
  · exact fun a j hj => (hA K P (p₁ ≫ q) _ (d + d') hZ a).1 j hj
  · intro c
    obtain ⟨e, he⟩ := hE c h₁ h₂
    refine ⟨e, fun a hc x y hx hy hz => ?_⟩
    have eq := hodge_pr_eq q q' p₁ p₂ hP.w.symm (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ hc hc x y
    have hz' : (CH.cx ((inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')).ι ⋙ G (p₁ ≫ q) c)).d c (cupU (p₁ ≫ q) _ hc hc ((morV p₁ rfl a h₁).pullC a x) ((morV p₂ hP.w.symm (c - a) h₂).pullC (c - a) y)) = 0 := by
      rw [← eq]
      exact hz
    exact (he a hc x y hx hy hz').trans (cls_eq _ eq.symm _ _)

end GlobalTheory.CompanionTheory.KunGlue.Aff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDoubleCosetIntersection
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

private theorem conj_apply_lemma (k : Type) [Field k] {N : ℕ} (w : Equiv.Perm (Fin N))
    (A : GL (Fin N) k) (u v : Fin N) :
    (↑(permGL k w * A * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) (w u) (w v) =
      (↑A : Matrix (Fin N) (Fin N) k) u v := by
  have hv : ∀ σ : Equiv.Perm (Fin N),
      (↑(permGL k σ) : Matrix (Fin N) (Fin N) k) = (σ⁻¹).toPEquiv.toMatrix := fun σ => rfl
  rw [← map_inv, Units.val_mul, Units.val_mul, hv, hv, inv_inv, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  simp [Matrix.submatrix_apply]

theorem GlobalTheory.CompanionTheory.GeomCell.innerMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (e' : (Σ j, m' j) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (w : Equiv.Perm (Fin N)) (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) (p : Levi k m') (hp : p ∈ relParab k g) (hx : permGL k w * leviEmb k e' p * (permGL k w)⁻¹ ∈ blockUpper k N β), ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨_, hx⟩ : levi k N β) : GL (Fin N) k) = leviEmb k e (relEmb k f (swapBlocks k c (relProj k g ⟨p, hp⟩))) := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ m' _ _ c _ _ e β hβ e' f g w hcell p hp hx
  have key : ∀ a b : Fin N, β a = β b ↔ blk e a = blk e b := by
    intro a b
    constructor
    · intro h
      rcases lt_trichotomy (blk e a) (blk e b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mpr h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mpr h'))
    · intro h
      rcases lt_trichotomy (β a) (β b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mp h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mp h'))
  have hL : ∀ x y, (↑(↑((GroundTheory.Automorphic.Parabolic.leviProj k N β) ⟨_, hx⟩ : levi k N β) :
      GL (Fin N) k) : Matrix (Fin N) (Fin N) k) x y = if β x = β y then
      (↑(permGL k w * leviEmb k e' p * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) x y else 0 :=
    fun x y => rfl
  have hrel : ∀ (Q : ∀ i, Levi k (c i)) (i : α), relEmb k f Q i = leviEmb k (f i) (Q i) :=
    fun Q i => rfl
  have hsw : ∀ (R : ∀ j, Levi k (fun i => c i j)) (i : α) (j : β'), swapBlocks k c R i j = R j i :=
    fun R i j => rfl
  have hproj : ∀ (j : β') (i : α) (s s' : c i j),
      (↑((relProj k g ⟨p, hp⟩) j i) : Matrix (c i j) (c i j) k) s s' =
        (↑(p j) : Matrix (m' j) (m' j) k) (g j ⟨i, s⟩) (g j ⟨i, s'⟩) :=
    fun j i s s' => leviProj_apply k (g j) _ i s s'
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := (f i).surjective a
  obtain ⟨⟨i', a'⟩, rfl⟩ := e.surjective y
  obtain ⟨⟨j', t'⟩, rfl⟩ := (f i').surjective a'
  rw [hL]
  by_cases hii : i = i'
  · subst hii
    rw [if_pos ((key _ _).mpr (by rw [blk_apply, blk_apply])), ← hcell i j t, ← hcell i j' t',
      conj_apply_lemma, hcell i j t, hcell i j' t', leviEmb_apply_same, hrel]
    by_cases hjj : j = j'
    · subst hjj
      rw [leviEmb_apply_same, leviEmb_apply_same, hsw, hproj]
    · rw [leviEmb_apply_ne k e' p hjj, leviEmb_apply_ne k (f i) _ hjj]
  · rw [if_neg (fun h => hii (by rw [key, blk_apply, blk_apply] at h; exact h)),
      leviEmb_apply_ne k e _ hii]
end

