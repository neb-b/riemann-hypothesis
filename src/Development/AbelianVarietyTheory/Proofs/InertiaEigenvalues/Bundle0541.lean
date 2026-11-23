module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0506
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCoordinatesOfPrismCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.SiteCoord

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem comp_assoc {R : Type} [CommRing R] {P₁ P₂ P₃ P₄ : Obj l R} (a : Hom P₃ P₄) (b : Hom P₂ P₃)
    (c : Hom P₁ P₂) : (a.comp b).comp c = a.comp (b.comp c) := Hom.ext' rfl

theorem map_mulVec (S : Strat bk d) {Y Y' : Obj l ↥(OL K)} (k : Hom Y Y') (g₁ g₂ : Hom bk.prism Y)
    (w : Fin d → Y.A) :
    (fun i => k.f ((S.ε g₁ g₂).mulVec w i)) = (S.ε (k.comp g₁) (k.comp g₂)).mulVec fun i => k.f (w i) := by
  funext i
  rw [RingHom.map_mulVec, S.ε_nat]
  rfl

theorem mulVec_map_add {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (w w' : Fin d → A) :
    M.mulVec (fun i => φ ((w + w') i)) = M.mulVec (fun i => φ (w i)) + M.mulVec (fun i => φ (w' i)) := by
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem mulVec_map_smul {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (c : A) (w : Fin d → A) : M.mulVec (fun i => φ ((c • w) i)) = φ c • M.mulVec (fun i => φ (w i)) := by
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem coords_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : P →ₛₗ[h.f] (Fin d → C.A)), (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i)) → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ v : P →ₛₗ[a.f] (Fin d → Q.A), ∀ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a → ∀ x, (fun i => h'.f (v x i)) = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) := by
  intro l _ K bk d S B C h f hC P _ _ u hu Q a g
  obtain ⟨Q₀, a₀, h₀, hpo⟩ := hC.stable.po Q a
  have hc₀ : Cover h₀ := (_root_.GlobalTheory.BSP.stable_cover_of_isPO l _ B C Q Q₀ h a a₀ h₀ hpo).2 hC
  obtain ⟨hinj, hsh⟩ := _root_.GlobalTheory.BSP.cover_injective_and_descent l _ Q Q₀ h₀ hc₀
  obtain ⟨D, p, q, hpq⟩ := hc₀.stable.po Q₀ h₀
  have hcf : ∀ b, a₀.f (h.f b) = h₀.f (a.f b) := fun b => congrArg (fun k : Hom B Q₀ => k.f b) hpo.comm
  obtain ⟨z, hzdef⟩ : ∃ z : P → Fin d → Q₀.A,
      z = fun x => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := ⟨_, rfl⟩
  have hpa : (p.comp a₀).comp h = (q.comp a₀).comp h := by
    rw [comp_assoc p a₀ h, comp_assoc q a₀ h, hpo.comm, ← comp_assoc p h₀ a, ← comp_assoc q h₀ a, hpq.comm]
  have hg : p.comp (h₀.comp g) = q.comp (h₀.comp g) := by rw [← comp_assoc p h₀ g, hpq.comm, comp_assoc q h₀ g]
  have key : ∀ x, (fun i => p.f (z x i)) = fun i => q.f (z x i) := by
    intro x
    have e1 := hu D (p.comp a₀) (q.comp a₀) hpa x
    simp only [comp_assoc] at e1
    have e1' : (fun i => p.f (a₀.f (u x i))) = (S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
        fun i => q.f (a₀.f (u x i)) := e1
    have e2 := map_mulVec S p (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have e3 := map_mulVec S q (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have hzx : z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := by rw [hzdef]
    calc (fun i => p.f (z x i))
        = fun i => p.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
          congrArg (fun w : Fin d → Q₀.A => fun i => p.f (w i)) hzx
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec fun i => p.f (a₀.f (u x i)) := e2
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec
            ((S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i))) :=
          congrArg (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec e1'
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f)) * S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
            fun i => q.f (a₀.f (u x i)) := Matrix.mulVec_mulVec _ _ _
      _ = (S.ε (p.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun M => Matrix.mulVec M fun i => q.f (a₀.f (u x i))) (S.ε_trans _ _ _)
      _ = (S.ε (q.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun k => Matrix.mulVec (S.ε k (q.comp (a₀.comp f))) fun i => q.f (a₀.f (u x i))) hg
      _ = fun i => q.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) := e3.symm
      _ = fun i => q.f (z x i) := (congrArg (fun w : Fin d → Q₀.A => fun i => q.f (w i)) hzx).symm
  have hz : ∀ x i, ∃ y, h₀.f y = z x i := fun x i => by
    obtain ⟨y, hy⟩ := hsh D p q hpq (z x i) (congrFun (key x) i)
    exact ⟨y, hy⟩
  choose y hy using hz
  have hzx : ∀ x, z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := fun x => congrFun hzdef x
  have z_add : ∀ x x', z (x + x') = z x + z x' := fun x x' =>
    calc z (x + x') = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (x + x') i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((u x + u x') i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i)) (map_add u x x')
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) +
            (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x' i)) := mulVec_map_add a₀.f _ _ _
      _ = z x + z x' := congrArg₂ (· + ·) (hzx x).symm (hzx x').symm
  have z_smul : ∀ (b : B.A) x, z (b • x) = h₀.f (a.f b) • z x := fun b x =>
    calc z (b • x) = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (b • x) i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((h.f b • u x) i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i))
            (LinearMap.map_smulₛₗ u b x)
      _ = a₀.f (h.f b) • (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) := mulVec_map_smul a₀.f _ _ _
      _ = h₀.f (a.f b) • z x := congrArg₂ (· • ·) (hcf b) (hzx x).symm
  let v : P →ₛₗ[a.f] (Fin d → Q.A) :=
    { toFun := y
      map_add' := fun x x' => by
        funext i
        apply hinj
        exact calc h₀.f (y (x + x') i) = z (x + x') i := hy _ i
          _ = z x i + z x' i := congrFun (z_add x x') i
          _ = h₀.f (y x i) + h₀.f (y x' i) := congrArg₂ (· + ·) (hy x i).symm (hy x' i).symm
          _ = h₀.f (y x i + y x' i) := (map_add h₀.f _ _).symm
      map_smul' := fun b x => by
        funext i
        apply hinj
        exact calc h₀.f (y (b • x) i) = z (b • x) i := hy _ i
          _ = h₀.f (a.f b) * z x i := congrFun (z_smul b x) i
          _ = h₀.f (a.f b) * h₀.f (y x i) := congrArg (h₀.f (a.f b) * ·) (hy x i).symm
          _ = h₀.f (a.f b * y x i) := (map_mul h₀.f _ _).symm }
  refine ⟨v, ?_⟩
  intro Q' h' a' hcomm x
  have hU := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C Q Q₀ h a a₀ h₀ hpo Q' a' h' hcomm
  obtain ⟨c, hc, -⟩ := hU
  have e : (fun i => h'.f (v x i)) = fun i => (c.comp h₀).f (y x i) :=
    congrArg (fun k : Hom Q Q' => fun i => k.f (y x i)) hc.2.symm
  have e' : (fun i => (c.comp h₀).f (y x i)) = fun i => c.f (z x i) := by
    funext i
    exact congrArg c.f (hy x i)
  exact calc (fun i => h'.f (v x i)) = fun i => c.f (z x i) := e.trans e'
    _ = fun i => c.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
        congrArg (fun w : Fin d → Q₀.A => fun i => c.f (w i)) (hzx x)
    _ = (S.ε (c.comp (h₀.comp g)) (c.comp (a₀.comp f))).mulVec fun i => c.f (a₀.f (u x i)) :=
        map_mulVec S c _ _ _
    _ = (S.ε ((c.comp h₀).comp g) ((c.comp a₀).comp f)).mulVec fun i => (c.comp a₀).f (u x i) :=
        congrArg₂ (fun k k' => (S.ε k k').mulVec fun i => c.f (a₀.f (u x i)))
          (comp_assoc c h₀ g).symm (comp_assoc c a₀ f).symm
    _ = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) :=
        congrArg₂ (fun (k : Hom Q Q') (k' : Hom C Q') => (S.ε (k.comp g) (k'.comp f)).mulVec fun i => k'.f (u x i))
          hc.2 hc.1

end GlobalTheory.BSP.SiteCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameOfFrobeniusDense
section
noncomputable section

namespace GlobalTheory.TypeLeaf.ConjPlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem mem_ine_of_wild {A : ValuationSubring Ω} {s : G E Ω}
    (hs : ∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) : s ∈ Ine (F := E) A := by
  have hv : ∀ y, A.valuation (s y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h1 : A.valuation (s y / y) = 1 := by
      have := Valuation.map_one_add_of_lt A.valuation (hs y hy)
      simpa using this
    rw [map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h1
    exact h1
  refine ⟨?_, fun x hx => ?_⟩
  · show s • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : s x - x = (s x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hs x hx0)

theorem tameGenAt_move (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (f : G E Ω →* G E Ω) (hf : ∀ σ x, f σ x = c (σ (c.symm x))) (hcont : Continuous f)
    {B : ValuationSubring Ω} {γ : G E Ω} (h : TameGenAt B γ) : TameGenAt (moveVal c B) (f γ) := by
  have e : ∀ σ, f σ = conjAut c hc σ := fun σ => AlgEquiv.ext (hf σ)
  refine ⟨by rw [e]; exact conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := conjAut_mem_ine c.symm hc' hσ
  have e2 : moveVal c.symm (moveVal c B) = B := by
    ext x
    simp [mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (conjAut c.symm hc' σ) := by
    ext x
    rw [hf, conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure hcont (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [moveVal_lt_one, map_sub, map_div₀, map_one, hf, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

theorem continuous_cConj (D : D7) : Continuous (cConj D.ntw) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff D.host.E D.nd.Om U).1 hU
  have h := isOpen_comap_cConj D.ntw (IntermediateField.fixingSubgroup_isOpen L)
  exact Filter.mem_map.2 (Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLU hg)

theorem exists_tameGenAt_conj (D : D7) {P w : PlE D.host} (h : IsConjPl D.host P w) {γ : G D.host.E D.nd.Om}
    (hγ : TameGenAt (D.nd.plOm.1 w) γ) :
    ∃ g : G D.host.E D.nd.Om, TameGenAt (D.nd.plOm.1 P) (g * cConj D.ntw γ * g⁻¹) := by
  have h2 := isPlaceOver_moveVal_cc D.ntw (isConjPl_symm h) (D.nd.plOm.2 w)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (D.nd.plOm.2 P)
  have h3 := tameGenAt_move D.ntw.cc (cc_symm_mem D.ntw) (fun x => ⟨_, cc_algebraMap D.ntw x⟩) (cConj D.ntw)
    (cConj_apply D.ntw) (continuous_cConj D) hγ
  have h4 := tameGenAt_move g.toRingEquiv (fun x => ⟨x, g.symm.commutes x⟩) (fun x => ⟨x, g.commutes x⟩)
    (MulAut.conj g).toMonoidHom (fun _ _ => rfl) (by
      change Continuous fun x => g * x * g⁻¹
      fun_prop) h3
  have e : moveVal g.toRingEquiv (moveVal D.ntw.cc (D.nd.plOm.1 w)) = D.nd.plOm.1 P := by
    rw [← hg]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [e] at h4
  exact ⟨g, h4⟩

section Alg

theorem charpoly_pow_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) (n : ℕ) :
    (A ^ n).charpoly = (s.map fun x => X - C (f x ^ n)).prod := by
  have h1 : A.charpoly.roots = s.map f := by
    rw [h, ← roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow K r n A
  rw [(IsAlgClosed.splits (A ^ n).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _), h2, h1,
    Multiset.map_map, Multiset.map_map]
  rfl

theorem pow_eq_one_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) {n : ℕ} (hn : A ^ n = 1)
    {x : ι} (hx : x ∈ s) : f x ^ n = 1 := by
  have h1 := charpoly_pow_of_prod A s f h n
  have h2 : (X - C (f x ^ n)) ∣ (A ^ n).charpoly := by
    rw [h1]
    exact Multiset.dvd_prod (Multiset.mem_map.2 ⟨x, hx, rfl⟩)
  rw [hn, Matrix.charpoly_one, dvd_iff_isRoot] at h2
  simp only [IsRoot.def, eval_pow, eval_sub, eval_X, eval_one] at h2
  exact sub_eq_zero.1 (eq_zero_of_pow_eq_zero h2)

variable {g : ℕ} [Fact g.Prime]

theorem map_zero_of_injective {θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g} (h : Function.Injective θ) : θ 0 = 0 := by
  by_contra h0
  have h1 : θ 0 * θ 0 = θ 0 * θ 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact zero_ne_one (h (mul_left_cancel₀ h0 h1))

theorem coprime_primeToPart {l : ℕ} (hl : l.Prime) (x : Formalism.CyclotomicNorms.Fbar g) (h : Formalism.CyclotomicNorms.primeToPart l x ≠ 0) :
    (orderOf (Formalism.CyclotomicNorms.primeToPart l x)).Coprime l := by
  rcases eq_or_ne x 0 with rfl | hx
  · unfold Formalism.CyclotomicNorms.primeToPart at h ⊢
    generalize (_ * _ : ℕ) = m at h ⊢
    rcases m with _ | m
    · simp
    · simp at h
  · have h0 : orderOf x ≠ 0 := (isOfFinOrder_of_ne_zero hx).orderOf_pos.ne'
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.coprime_ordCompl hl h0).symm
    unfold Formalism.CyclotomicNorms.primeToPart
    rw [pow_mul]
    refine (orderOf_pow_dvd _).trans ?_
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd _ _)]

theorem comp_pow_eq {K : Type} [Field K] {l M n : ℕ} (hl : l.Prime) (hM : 0 < M) {ι : Formalism.CyclotomicNorms.Fbar g →* K}
    (hι : InjPrimeTo l ι) {θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g} (hθ : Function.Injective θ)
    (hθn : ∀ x, x ^ M = 1 → θ x = x ^ n) {e : ℤ} (he : e = 1 ∨ e = -1) (x : Formalism.CyclotomicNorms.Fbar g)
    (h : (ι (Formalism.CyclotomicNorms.primeToPart l x) ^ e) ^ M = 1) :
    (ι.comp θ) (Formalism.CyclotomicNorms.primeToPart l x) ^ e = (ι (Formalism.CyclotomicNorms.primeToPart l x) ^ e) ^ n := by
  have hc := coprime_primeToPart hl x
  set y := Formalism.CyclotomicNorms.primeToPart l x
  have h1 : ι y ^ M = 1 := by
    rcases he with rfl | rfl
    · simpa using h
    · simpa using h
  have h2 : ι (θ y) = ι y ^ n := by
    rcases eq_or_ne y 0 with hy | hy
    · have h0 : ι y ≠ 0 := fun h0 => by
        rw [h0, zero_pow hM.ne'] at h1
        exact zero_ne_one h1
      have h3 : ι y * ι y = ι y * 1 := by rw [← map_mul, hy, zero_mul, mul_one]
      have h4 := mul_left_cancel₀ h0 h3
      rw [h4, one_pow, hy, map_zero_of_injective hθ, ← hy, h4]
    · have h3 : y ^ M = 1 := hι _ _ (pow_ne_zero _ hy) one_ne_zero
        (Nat.Coprime.coprime_dvd_left (orderOf_pow_dvd _) (hc hy)) (by simp) (by rw [map_pow, h1, map_one])
      rw [hθn y h3, map_pow]
  rw [MonoidHom.comp_apply, h2, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem injPrimeTo_comp {K : Type} [Field K] {l : ℕ} {ι : Formalism.CyclotomicNorms.Fbar g →* K}
    (hι : InjPrimeTo l ι) {θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g} (hθ : Function.Injective θ)
    (ho : ∀ x, orderOf (θ x) = orderOf x) : InjPrimeTo l (ι.comp θ) := by
  have hne : ∀ x, x ≠ 0 → θ x ≠ 0 := fun x hx h => hx (hθ (h.trans (map_zero_of_injective hθ).symm))
  intro x y hx hy cx cy h
  exact hθ (hι _ _ (hne x hx) (hne y hy) (by rwa [ho]) (by rwa [ho]) h)

end Alg

def chiBar (D : D7) (i : D.nd.Loc) : G D.host.E D.nd.Om →* (Formalism.CyclotomicNorms.Fbar (D.nd.l i))ˣ :=
  (Units.map ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i 1)

theorem chiBar_val (D : D7) (i : D.nd.Loc) (s : G D.host.E D.nd.Om) :
    (chiBar D i s : Formalism.CyclotomicNorms.Fbar (D.nd.l i)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i s)) := rfl

theorem isOpen_ker_chiBar (D : D7) (i : D.nd.Loc) : IsOpen ((chiBar D i).ker : Set (G D.host.E D.nd.Om)) := by
  have h := (isAdic_iff.1 (D.nd.O_adic i)).1 1
  rw [pow_one] at h
  have hc : Continuous fun s : G D.host.E D.nd.Om => chi1 D.nd i s - 1 := (D.nd.chi_cont i 1).sub continuous_const
  have e : ((chiBar D i).ker : Set (G D.host.E D.nd.Om)) =
      (fun s => chi1 D.nd i s - 1) ⁻¹' (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext s
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, chiBar_val, Units.val_one, Set.mem_preimage,
      SetLike.mem_coe, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero,
      map_eq_one_iff _ (D.naut.kFbar i).injective]
  rw [e]
  exact h.preimage hc

end GlobalTheory.TypeLeaf.ConjPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateCharacterFiniteOnInertiaOfEigenvector
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.TateEigen

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pos : 0 < ‖((l : ℕ) : ℤ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_l_lt_one : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem exists_pow_near_one (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : ℤ_[l]ˣ, ‖((u ^ N : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨Nat.card (ZMod (l ^ k))ˣ, Nat.card_pos, fun u => ?_⟩
  have h : (Units.map (PadicInt.toZModPow (p := l) k).toMonoidHom u) ^ Nat.card (ZMod (l ^ k))ˣ = 1 :=
    pow_card_eq_one'
  have h2 : ((u ^ Nat.card (ZMod (l ^ k))ˣ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := l) k) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    rw [← map_pow] at h
    exact congrArg Units.val h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  rw [hw, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)

theorem exists_norm_eq_pow (x : ℤ_[l]) (hx : x ≠ 0) : ∃ k : ℕ, ‖x‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  refine ⟨x.valuation, ?_⟩
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow]

theorem finite_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 →
    (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) →
    ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  intro l _ η y hy hη
  obtain ⟨c, hc, hax⟩ := _root_.GlobalTheory.AxLemma.ax_lemma_complete l
  have hτ0 := norm_l_pos (l := l)
  have hτ1 := norm_l_lt_one (l := l)
  set τ := ‖((l : ℕ) : ℤ_[l])‖ with hτ
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hτ1
  obtain ⟨N, hN, hNu⟩ := exists_pow_near_one (l := l) (k₁ + 2)
  refine ⟨N, hN, fun γ₀ hγ₀ => ?_⟩
  by_contra hne
  set γ := γ₀ ^ N with hγdef
  have hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := pow_mem hγ₀ N
  have hηγ : η γ = η γ₀ ^ N := map_pow _ _ _
  have hne' : (η γ : ℤ_[l]) - 1 ≠ 0 := by
    intro h
    apply hne
    rw [← hηγ]
    exact Units.ext (sub_eq_zero.1 h)
  obtain ⟨k, hk⟩ := exists_norm_eq_pow _ hne'
  have hkk : k₁ + 2 ≤ k := by
    have := hNu (η γ₀)
    rw [← hηγ, hk] at this
    exact (pow_le_pow_iff_right_of_lt_one₀ hτ0 hτ1).1 this
  have hk2 : 2 ≤ k := by omega
  obtain ⟨H, hmem, hnorm, hidx, hidx', hpow, hgen⟩ := _root_.GlobalTheory.galois_congruence_chain l η γ k hk2 hk
  obtain ⟨ρ, hρ0, hρ1, hgain⟩ := _root_.GlobalTheory.PartialTraceGain.norm_sum_pow_le l γ hγ H k hnorm hidx hidx' hpow hgen
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hρ1
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hr : 0 < τ ^ (k + n) * ‖y‖ := by positivity
  obtain ⟨z, hz, hyz⟩ := hax (H n) y (τ ^ (k + n) * ‖y‖) hr (by
    intro g hg
    have e : Per.σC g y - y = algebraMap ℚ_[l] ℂ_[l] ((((η g : ℤ_[l]) - 1 : ℤ_[l])) : ℚ_[l]) * y := by
      rw [hη g, PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]; ring
    rw [e, norm_mul, norm_algebraMap']
    exact mul_le_mul_of_nonneg_right ((hmem n g).1 hg) hy0.le)
  have hv : ∀ g ∈ H n, g (γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z) =
      γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z := by
    intro g hg
    have h1 := hz _ ((hnorm n).conj_mem' g hg γ)
    have h2 : g (γ z) = γ z := by
      have := congrArg γ h1
      simpa [mul_assoc] using this
    rw [map_sub, map_mul, h2, hz g hg, AlgEquiv.commutes]
  have hest := _root_.GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate l γ ((η γ : ℤ_[l]) : ℚ_[l]) y z (l ^ n) (c * (τ ^ (k + n) * ‖y‖)) (ρ ^ n)
    (hη γ) (PadicInt.norm_units (η γ)) (hz _ (hpow n)) hyz (hgain n _ hv) (by positivity)
  have hlte := GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l (η γ : ℤ_[l]) k hk2 hk n
  have e1 : ‖((η γ : ℤ_[l]) : ℚ_[l]) ^ l ^ n - 1‖ = τ ^ (k + n) := by
    rw [hτ, ← hlte, PadicInt.norm_def]; push_cast; rfl
  have e2 : ‖((η γ : ℤ_[l]) : ℚ_[l]) - 1‖ = τ ^ k := by
    rw [hτ, ← hk, PadicInt.norm_def]; push_cast; rfl
  rw [e1, e2] at hest
  have hk' : τ ^ k < c⁻¹ := lt_of_le_of_lt (pow_le_pow_of_le_one hτ0.le hτ1.le (by omega)) hk₁
  have key : ∀ a : ℝ, a < c⁻¹ → a * (c * (τ ^ (k + n) * ‖y‖)) < τ ^ (k + n) * ‖y‖ := by
    intro a ha
    have : a * c < 1 := by
      have := mul_lt_mul_of_pos_right ha hc
      rwa [inv_mul_cancel₀ hc.ne'] at this
    rw [← mul_assoc]
    exact mul_lt_of_lt_one_left hr this
  exact absurd hest (not_le.2 (max_lt (key _ hk') (key _ hn)))

end GlobalTheory.TateEigen
end

