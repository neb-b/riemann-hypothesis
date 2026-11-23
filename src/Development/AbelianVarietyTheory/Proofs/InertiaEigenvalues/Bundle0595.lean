module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRealizationMatrixStratifiedPhiModule
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RealMatrix

section Alg

variable {R R' : Type} [CommRing R] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom (f : R →+* R') (c : R) (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_matrix_equation_inverse_scaling (F : R →+* R) (e t v : R) (hv : v * t = 1) (ht : F t = e * t) (a N : ℕ) (Y A : Matrix n n R)
    (h : e ^ a • Y.map F = Y * A) : e ^ (a + N) • (v ^ N • Y).map F = (v ^ N • Y) * A := by
  have h1 : F v * (e * t) = 1 := by rw [← ht, ← map_mul, hv, map_one]
  have h2 : e * F v = v := by linear_combination v * h1 - (e * F v) * hv
  have h3 : e ^ (a + N) * F v ^ N = v ^ N * e ^ a := by
    rw [pow_add, mul_assoc, ← mul_pow, h2, mul_comm]
  rw [map_smul_hom, map_pow, smul_smul, h3, ← smul_smul, h, Matrix.smul_mul]

theorem galois_matrix_equation_inverse_scaling (G : R →+* R) (t v : R) (hv : v * t = 1) (N : ℕ) (P Y ε : Matrix n n R)
    (h : t ^ N • (P * Y.map G) = G t ^ N • (Y * ε)) : P * (v ^ N • Y).map G = (v ^ N • Y) * ε := by
  have h1 : G v * G t = 1 := by rw [← map_mul, hv, map_one]
  have h2 := congrArg (fun M => (v ^ N * G v ^ N) • M) h
  have h3 : v ^ N * G v ^ N * t ^ N = G v ^ N := by
    rw [mul_right_comm, ← mul_pow, hv, one_pow, one_mul]
  have h4 : v ^ N * G v ^ N * G t ^ N = v ^ N := by
    rw [mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  simp only [smul_smul, h3, h4] at h2
  rw [map_smul_hom, map_pow, Matrix.mul_smul, h2, Matrix.smul_mul]

theorem descend (f : R →+* R') (hf : Function.Injective f) (x y : R) (N : ℕ) (M Y ε : Matrix n n R)
    (h : f x ^ N • M.map f = f y ^ N • (Y.map f * ε.map f)) : x ^ N • M = y ^ N • (Y * ε) := by
  apply Matrix.map_injective hf
  simp only []
  rw [map_smul_hom, map_smul_hom, map_pow, map_pow, Matrix.map_mul, h]

theorem push (f : R →+* R') (x y : R) (N : ℕ) (P Q Y ε : Matrix n n R) (h : x ^ N • (P * Q) = y ^ N • (Y * ε)) :
    f x ^ N • (P.map f * Q.map f) = f y ^ N • (Y.map f * ε.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_pow, ← map_pow, ← map_smul_hom, ← map_smul_hom, h]

end Alg

theorem exists_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  intro l _ K bk d ρ τ s ht hτ S ha hA hrel
  obtain ⟨u, hu⟩ := (_root_.GlobalTheory.BSP.isUnit_inclW_per_and_saturated l K bk τ hτ).1
  have hv : (↑u⁻¹ : WCb l) * inclW l τ = 1 := by rw [← hu, Units.inv_mul]
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine ⟨(↑u⁻¹ : WCb l) ^ s.N • ht.Y.map (inclW l), ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (((Units.isUnit _).pow _).map _).mul ht.unit
  · rw [ha, hA]
    refine frobenius_matrix_equation_inverse_scaling (frobW l : WCb l →+* WCb l) (bk.evW bk.E) (inclW l τ) _ hv ?_ _ _ _ _ ?_
    · change frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ
      rw [frobW_inclW, hτ.1, map_mul]
    · have h := congrArg (fun M => M.map (inclW l)) ht.φ
      try beta_reduce at h
      rw [map_smul_hom, map_pow, Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext1 i j
      exact frobW_inclW _
  · intro g
    have h0 := descend bk.iA hinj _ _ _ _ _ _ (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g _ (hrel g))
    have h := push (inclW l) _ _ _ _ _ _ _ h0
    rw [← galW_inclW] at h
    refine galois_matrix_equation_inverse_scaling (galW l (g : GQ l) : WCb l →+* WCb l) (inclW l τ) _ hv _ _ _ _ ?_
    refine Eq.trans ?_ h
    congr 2
    · ext1 i j
      exact ((inclWA l).commutes _).symm
    · ext1 i j
      exact galW_inclW _ _

end GlobalTheory.BSP.RealMatrix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleValue
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EvalEx

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P] {f : A →+* B} {g : B →+* C} {k : A →+* C}
    (u : M →ₛₗ[f] N) (t : N →ₛₗ[g] P) (w : M →ₛₗ[k] P) (hk : ∀ a, k a = g (f a)) (hw : ∀ x, w x = t (u x))
    (hu : SemiBC u) (ht : SemiBC t) : SemiBC w := by
  intro Q _ _ v
  letI : Module B Q := Module.compHom Q g
  let v' : M →ₛₗ[f] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun a x => by
        change v (a • x) = g (f a) • v x
        rw [v.map_smulₛₗ, hk] }
  obtain ⟨z, hz, hzu⟩ := hu Q v'
  let z' : N →ₛₗ[g] Q :=
    { toFun := z
      map_add' := z.map_add
      map_smul' := fun b n => z.map_smul b n }
  obtain ⟨y, hy, hyu⟩ := ht Q z'
  refine ⟨y, fun x => by rw [hw, hy]; exact hz x, fun y' hy' => hyu y' fun n => ?_⟩
  let r : N →ₗ[B] Q :=
    { toFun := fun n => y' (t n)
      map_add' := fun n n' => by simp only [map_add (f := _)]
      map_smul' := fun b n => by
        change y' (t (b • n)) = g b • y' (t n)
        rw [t.map_smulₛₗ, y'.map_smul] }
  have := hzu r fun x => by
    change y' (t (u x)) = v x
    rw [← hw]; exact hy' x
  exact LinearMap.congr_fun this n

theorem ε_mulVec {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B : Obj l ↥(OL K)}
    (f g h : Hom bk.prism B) (v : Fin d → B.A) :
    (S.ε f g).mulVec ((S.ε g h).mulVec v) = (S.ε f h).mulVec v := by
  rw [Matrix.mulVec_mulVec, S.ε_trans]

theorem hom_comp_assoc {l : ℕ} {R : Type} [CommRing R] {X Y Z W : Obj l R} (p : Hom Z W) (q : Hom Y Z)
    (r : Hom X Y) : (p.comp q).comp r = p.comp (q.comp r) := Hom.ext' rfl

end GlobalTheory.BSP.EvalEx

namespace GlobalTheory.BSP

theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module B.A N), Nonempty (Eval S B N) := by
  intro l _ K bk d S B
  obtain ⟨C, h, ⟨f⟩, hc⟩ := _root_.GlobalTheory.BSP.exists_cover_receiving_bk l K bk B
  obtain ⟨P, _, _, _, _, u, hu, hcoc⟩ := _root_.GlobalTheory.BSP.CoverDesc.exists_descent l K bk d S B C h f hc
  have hv := _root_.GlobalTheory.BSP.SiteCoord.coords_of_cover l K bk d S B C h f hc P u hcoc
  choose vv hvv using hv
  have po : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q), ∃ (Q₀ : Obj l ↥(OL K)) (a₀ : Hom C Q₀) (h₀ : Hom Q Q₀),
      a₀.comp h = h₀.comp a ∧ Cover h₀ ∧ Function.Injective h₀.f := by
    intro Q a
    obtain ⟨Q₀, a₀, h₀, hpo⟩ := hc.stable.po Q a
    have hc₀ := (_root_.GlobalTheory.BSP.stable_cover_of_isPO l _ B C Q Q₀ h a a₀ h₀ hpo).2 hc
    exact ⟨Q₀, a₀, h₀, hpo.comm, hc₀, (_root_.GlobalTheory.BSP.cover_injective_and_descent l _ Q Q₀ h₀ hc₀).1⟩
  refine ⟨P, inferInstance, inferInstance, ⟨{
    fin := inferInstance
    proj := inferInstance
    v := fun {Q} a g => vv Q a g
    bc := ?_
    v_ε := ?_
    v_nat := ?_ }⟩⟩
  · intro Q a g
    obtain ⟨Q₀, a₀, h₀, hcomm, hc₀, -⟩ := po Q a
    have hf : ∀ y, a₀.f (h.f y) = h₀.f (a.f y) := fun y => congrArg (fun φ : Hom B Q₀ => φ.f y) hcomm
    have hE1 : S.ε (h₀.comp g) (a₀.comp f) * S.ε (a₀.comp f) (h₀.comp g) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    have hE2 : S.ε (a₀.comp f) (h₀.comp g) * S.ε (h₀.comp g) (a₀.comp f) = 1 := by
      rw [S.ε_trans, S.ε_refl]
    let s : (Fin d → Q₀.A) ≃ₗ[Q₀.A] (Fin d → Q₀.A) :=
      { toFun := (S.ε (h₀.comp g) (a₀.comp f)).mulVec
        invFun := (S.ε (a₀.comp f) (h₀.comp g)).mulVec
        map_add' := Matrix.mulVec_add _
        map_smul' := fun c x => Matrix.mulVec_smul _ c x
        left_inv := fun x => by
          change (S.ε (a₀.comp f) (h₀.comp g)).mulVec ((S.ε (h₀.comp g) (a₀.comp f)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE2, Matrix.one_mulVec]
        right_inv := fun x => by
          change (S.ε (h₀.comp g) (a₀.comp f)).mulVec ((S.ε (a₀.comp f) (h₀.comp g)).mulVec x) = x
          rw [Matrix.mulVec_mulVec, hE1, Matrix.one_mulVec] }
    let w0 : P →ₛₗ[h₀.f.comp a.f] (Fin d → Q₀.A) :=
      { toFun := fun x j => a₀.f (u x j)
        map_add' := fun x y => by funext j; simp only [map_add (f := _), Pi.add_apply]
        map_smul' := fun b x => by
          funext j
          simp only [LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.comp_apply, hf] }
    have hw0 : SemiBC w0 := EvalEx.semiBC_comp u (piMap a₀.f (Fin d)) w0 (fun y => (hf y).symm)
      (fun x => rfl) hu (semiBC_piMap a₀.f _)
    exact _root_.GlobalTheory.BSP.semiBC_of_cover l _ Q Q₀ h₀ hc₀ B.A a.f P (Fin d → Q.A) (Fin d → Q₀.A) (vv Q a g)
      (piMap h₀.f (Fin d)) (s.toLinearMap.comp w0) (fun x => (hvv Q a g Q₀ h₀ a₀ hcomm x).symm)
      (semiBC_piMap h₀.f _) (hw0.comp_equiv s)
  · intro Q a g g' x
    obtain ⟨Q₀, a₀, h₀, hcomm, -, hinj⟩ := po Q a
    funext i
    apply hinj
    have e1 := congrFun (hvv Q a g Q₀ h₀ a₀ hcomm x) i
    have e2 := hvv Q a g' Q₀ h₀ a₀ hcomm x
    rw [e1, RingHom.map_mulVec, S.ε_nat,
      show (⇑h₀.f ∘ (vv Q a g') x) = fun i => h₀.f ((vv Q a g') x i) from rfl, e2]
    exact congrFun (EvalEx.ε_mulVec S (h₀.comp g) (h₀.comp g') (a₀.comp f) _).symm i
  · intro Q Q' c a g x i
    have hp := po Q' (c.comp a)
    obtain ⟨Q₁, a₁, h₁, hcomm, -, hinj⟩ := hp
    apply hinj
    have e1 := congrFun (hvv Q' (c.comp a) (c.comp g) Q₁ h₁ a₁ hcomm x) i
    have e2 := congrFun (hvv Q a g Q₁ (h₁.comp c) a₁ (hcomm.trans (EvalEx.hom_comp_assoc h₁ c a).symm) x) i
    have e3 : (h₁.comp c).f ((vv Q a g) x i) = h₁.f (c.f ((vv Q a g) x i)) := rfl
    refine e1.trans (Eq.trans ?_ (e3 ▸ e2).symm)
    exact congrArg (fun φ => (S.ε φ (a₁.comp f)).mulVec (fun j => a₁.f (u x j)) i)
      (EvalEx.hom_comp_assoc h₁ c g).symm

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FCrystalHomEqOfEtaleRealisationPerfectPrism
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem fHom_eq_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T']
    (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K))
    (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')),
    Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M',
      (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  intro l _ K T' _ _ ρ' M M' j' H u u' h
  obtain ⟨bk⟩ := _root_.GlobalTheory.BSP.nonempty_bk_of_finExt l K
  apply _root_.GlobalTheory.BSP.fhom_ext_bk l K bk M M' u u'
  haveI := M'.fin (ainfObj K)
  haveI := M'.proj (ainfObj K)
  haveI := M'.fin bk.prism
  haveI := M'.proj bk.prism
  have hj : Function.Injective j' :=
    semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom)
      (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc
  have ht : Function.Injective (M'.tr bk.ι) :=
    semiBC_injective_of_injective _ _ bk.ι.f (_root_.GlobalTheory.BSP.bk_ev_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)
  refine LinearMap.ext fun x => ht (hj ?_)
  rw [← u.u_tr, ← u'.u_tr]
  exact h _

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAll

theorem split_equiv {G L V₀ V₁ V₂ : Type} [Group G] [Field L] [AddCommGroup V₀] [Module L V₀]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂]
    (ρ₀ : Representation L G V₀) (ρ₁ : Representation L G V₁) (ρ₂ : Representation L G V₂)
    (ι : V₀ →ₗ[L] V₁) (π : V₁ →ₗ[L] V₂) (hι : ∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x))
    (hi : Function.Injective ι) (hk : LinearMap.range ι = LinearMap.ker π)
    (s : V₂ →ₗ[L] V₁) (hs : ∀ g x, s (ρ₂ g x) = ρ₁ g (s x)) (hps : ∀ x, π (s x) = x) :
    ∃ e : V₁ ≃ₗ[L] (V₀ × V₂), ∀ g v, e (ρ₁ g v) = (ρ₀ g (e v).1, ρ₂ g (e v).2) := by
  let f : V₀ × V₂ →ₗ[L] V₁ := ι.coprod s
  have hf : ∀ a b, f (a, b) = ι a + s b := fun a b => rfl
  have hπι : ∀ a, π (ι a) = 0 := fun a => by
    have : ι a ∈ LinearMap.ker π := hk ▸ LinearMap.mem_range_self ι a
    exact this
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ h
      rw [hf] at h
      have hb : b = 0 := by
        have := congrArg π h
        rwa [map_add, hπι, hps, zero_add, map_zero] at this
      subst hb
      rw [map_zero, add_zero] at h
      have ha : a = 0 := hi (by rw [h, map_zero])
      rw [ha]; rfl
    · intro z
      have hz : z - s (π z) ∈ LinearMap.range ι := by
        rw [hk, LinearMap.mem_ker, map_sub, hps, sub_self]
      obtain ⟨a, ha⟩ := hz
      exact ⟨(a, π z), by rw [hf, ha, sub_add_cancel]⟩
  let e := (LinearEquiv.ofBijective f hbij).symm
  refine ⟨e, fun g v => ?_⟩
  apply (LinearEquiv.ofBijective f hbij).injective
  change f (e (ρ₁ g v)) = f (ρ₀ g (e v).1, ρ₂ g (e v).2)
  have h1 : ∀ w, f (e w) = w := fun w => (LinearEquiv.ofBijective f hbij).apply_symm_apply w
  rw [h1, hf, hι, hs, ← map_add (f := _), ← hf]
  have : ((e v).1, (e v).2) = e v := rfl
  rw [this, h1]

theorem fontaineAt_all : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL) := by
  intro D l _ K LL
  have T := D.locT l
  unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A₀ A₁ A₂ ι π hι hπ hi hs hk
    refine ⟨?_, ?_⟩
    · intro h1
      have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ ι hι).1 hi h1
      have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₂.V A₂.ρ π hπ).2 hs h1).1
      have d1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ h1).1
      obtain ⟨-, -, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ
        A₂.V A₂.ρ ι π hι hπ hi hs hk d1
      exact ⟨c0, c2, fun τ a => (hm τ a).2.1⟩
    · rintro ⟨s, hs', hps⟩ h0 h2
      obtain ⟨e, he⟩ := split_equiv A₀.ρ A₁.ρ A₂.ρ ι π hι hi hk s hs' hps
      exact ((GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₀.V A₀.ρ
        A₂.V A₂.ρ e he).2.1).2 ⟨h0, h2⟩
  · intro A A' χ htw hχ hA
    exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ χ htw hχ hA
  · intro A A' P hD hA
    exact GlobalTheory.DualOne.isCrys_of_isDual1 l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ P hD hA
  · intro A hA
    exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A.V A.ρ hA).1

end GlobalTheory.FontaineAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorus
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem sigmaFinite_comap_of_measurable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y)
    (hf : Measurable f) (μ : Measure Y) [SigmaFinite μ] : SigmaFinite (μ.comap f) := by
  by_cases h : Function.Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · refine ⟨⟨⟨fun n => f ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.comap_apply₀ f μ h.1 h.2 ((measurableSet_spanningSets μ n).preimage hf).nullMeasurableSet]
      exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  · rw [Measure.comap, dite_eq_right h]; infer_instance

theorem fubini_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  intro F E _ _ _ _ _ A r τ p hG M μK hμK α Φ hΦ hαlc hαcs hα0 c h1
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  obtain ⟨hBor, hHaar, -⟩ := GlobalTheory.JR.LinDesc.unitsMeas_isHaar F E A μK hμK
  haveI := hBor
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) F) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin r) F) := Units.isEmbedding_embedProduct.t2Space
  have e := (LinDesc.bas A hG).equivFun
  have he1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  haveI : SecondCountableTopology A.K := (Homeomorph.mk e.toEquiv he1 he2).secondCountableTopology
  haveI : SigmaFinite μK := inferInstance
  haveI : SigmaFinite (LinDesc.unitsMeas A μK) := by
    unfold LinDesc.unitsMeas
    haveI : SigmaFinite (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹) :=
      SigmaFinite.withDensity_ofReal _
    exact sigmaFinite_comap_of_measurable _ (measurable_iff_comap_le.2 le_rfl) _
  have htm : Continuous (LinDesc.tm A hG) := Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (LinDesc.bas A hG)).toLinearMap)
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hαc : Continuous α := hαlc.continuous
  have hC : IsCompact (tsupport Φ) := hΦ.2
  have hz : ∀ g, g ∉ tsupport Φ → Φ g = 0 := fun g hg => image_eq_zero_of_notMem_tsupport hg
  haveI : IsFiniteMeasure (M.μG.restrict (tsupport Φ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  set ν := LinDesc.unitsMeas A μK with hν
  set f : A.Kˣ → GL (Fin r) F → ℂ := fun s g => Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) with hf
  have hfc : Continuous (Function.uncurry f) := by
    refine (hΦc.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hαc.comp ?_))
    exact (continuous_snd.mul continuous_const).mul (htm.comp continuous_fst)
  have hin : ∀ g, Integrable (fun s => f s g) ν := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · have hi : Integrable (fun s => α (g * c * LinDesc.tm A hG s)) ν :=
        Integrable.of_integral_ne_zero (by rw [h1 g hg]; exact one_ne_zero)
      exact hi.ofReal.const_mul (Φ g)
  have hnorm : ∀ g, ∫ s, ‖f s g‖ ∂ν = ‖Φ g‖ := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · simp only [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hα0 _)]
      rw [integral_const_mul, h1 g hg, mul_one]
  have hint : Integrable (Function.uncurry f) (ν.prod (M.μG.restrict (tsupport Φ))) := by
    rw [integrable_prod_iff' hfc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hin, ?_⟩
    exact (hΦc.norm.continuousOn.integrableOn_compact hC).congr (Eventually.of_forall fun g => (hnorm g).symm)
  have eL : ∀ s, ∫ g, f s g ∂M.μG = ∫ g in tsupport Φ, f s g ∂M.μG := fun s =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => by simp [hf, hz g hg]).symm
  have eR : ∫ g, Φ g ∂M.μG = ∫ g in tsupport Φ, Φ g ∂M.μG :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => hz g hg).symm
  show ∫ s, ∫ g, f s g ∂M.μG ∂ν = ∫ g, Φ g ∂M.μG
  simp_rw [eL, eR]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : Φ g = 0
  · simp [hf, hg]
  · simp only [hf]
    rw [integral_const_mul, integral_complex_ofReal, h1 g hg, Complex.ofReal_one, mul_one]

end GlobalTheory.JR.LinDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryMemLatticeInvLOfMonodromyEqZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem coboundary_mem_lattice_of_mon_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hy hMon b hb g hg
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.BKGal.gb_sub_b_mem_filZero l a e O K t ϖ hl2 ι η H D T R y hy hMon b hb g hg
  exact _root_.GlobalTheory.CrisFixedLattice.exists_pow_smul_eq_one_tmul hF l O K (Gl l) T C _ (_root_.GlobalTheory.BKGal.PhiFix.frob_fixed_coboundary l a e O K t ϖ ι η H D T R y hy b hb g hg) hC

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBasis_frobenius_equation_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  first | exact @GlobalTheory.BSP.Height.bas_frob | exact GlobalTheory.BSP.Height.bas_frob | (intros; apply GlobalTheory.BSP.Height.bas_frob <;> assumption)
end

