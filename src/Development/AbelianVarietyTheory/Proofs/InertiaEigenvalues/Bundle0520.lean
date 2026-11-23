module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevel
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmithFormCoefficientRingImageOrPrimeDvdRow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SmithOE

theorem pid_dichotomy {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (d : ℕ)
    (P : Matrix (Fin d) (Fin d) O) :
    ∃ U W : Matrix (Fin d) (Fin d) O, W * U = 1 ∧ U * W = 1 ∧
      ∀ j, (∃ w : Fin d → O, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, ¬ IsUnit ((W * P) j k)) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin P)).smithNormalForm (Pi.basisFun O (Fin d))
  set U : Matrix (Fin d) (Fin d) O := (Pi.basisFun O (Fin d)).toMatrix snf.bM with hUdef
  set W : Matrix (Fin d) (Fin d) O := snf.bM.toMatrix (Pi.basisFun O (Fin d)) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  refine ⟨U, W, hWU, hUW, fun j => ?_⟩
  have hUcol : (fun i => U i j) = (snf.bM j : Fin d → O) := by
    funext i
    simp [hUdef, Module.Basis.toMatrix_apply]
  have hmem : ∀ k, (fun i => P i k) ∈ LinearMap.range (Matrix.mulVecLin P) := fun k =>
    ⟨Pi.single k 1, by funext i; simp⟩
  have hWP : ∀ k, (W * P) j k = snf.bM.repr (fun i => P i k) j := by
    intro k
    have h := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O (Fin d)) snf.bM (fun i => P i k)
    rw [← h, ← hWdef]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  by_cases h : ∃ i, snf.f i = j ∧ IsUnit (snf.a i)
  · obtain ⟨i, rfl, u, hu⟩ := h
    left
    have hN : (snf.bM (snf.f i) : Fin d → O) ∈ LinearMap.range (Matrix.mulVecLin P) := by
      have h1 : (snf.bM (snf.f i) : Fin d → O) = (↑u⁻¹ : O) • (snf.bN i : Fin d → O) := by
        rw [snf.snf, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (snf.bN i).2
    obtain ⟨w, hw⟩ := hN
    exact ⟨w, by rw [hUcol, ← hw]; rfl⟩
  · right
    intro k
    rw [hWP k]
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      have h2 := congrFun (snf.repr_comp_embedding_eq_smul ⟨_, hmem k⟩) i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : snf.bM.repr (fun i => P i k) (snf.f i) = snf.a i * snf.bN.repr ⟨_, hmem k⟩ i := h2
      rw [h3]
      intro hu
      exact h ⟨i, rfl, isUnit_of_mul_isUnit_left hu⟩
    · have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem k⟩ hj
      have h0' : snf.bM.repr (fun i => P i k) j = 0 := h0
      rw [h0']
      exact not_isUnit_zero

end GlobalTheory.SmithOE

namespace GlobalTheory.SmithOE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE → ∀ (d' : ℕ) (P : Matrix (Fin d') (Fin d') (WCb l)), (∀ i j, P i j ∈ bk.OE) → ∃ U Uinv : Matrix (Fin d') (Fin d') (WCb l), (∀ i j, U i j ∈ bk.OE) ∧ (∀ i j, Uinv i j ∈ bk.OE) ∧ Uinv * U = 1 ∧ U * Uinv = 1 ∧ ∀ j, (∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, (l : WCb l) ∣ (Uinv * P) j k) := by
  intro l _ K bk _ d' P hP
  have hfac := (GlobalTheory.OEDvr.main l K bk).2.2.2.1
  let P' : Matrix (Fin d') (Fin d') ↥bk.OE := Matrix.of fun i j => ⟨P i j, hP i j⟩
  obtain ⟨U', W', hWU, hUW, hdich⟩ := pid_dichotomy d' P'
  have hP'map : P'.map bk.OE.subtype = P := by ext; rfl
  refine ⟨U'.map bk.OE.subtype, W'.map bk.OE.subtype, fun i j => (U' i j).2, fun i j => (W' i j).2,
    ?_, ?_, fun j => ?_⟩
  · rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases hdich j with ⟨w, hw⟩ | hnu
    · left
      refine ⟨fun i => (w i : WCb l), ?_⟩
      rw [← hP'map]
      funext i
      have := congrArg Subtype.val (congrFun hw i)
      rw [Matrix.mulVec, dotProduct] at this ⊢
      simpa using this
    · right
      intro k
      have heq : ((W'.map bk.OE.subtype) * P) j k = (((W' * P') j k : ↥bk.OE) : WCb l) := by
        rw [← hP'map, ← Matrix.map_mul]; rfl
      rw [heq]
      have hk := hnu k
      generalize (W' * P') j k = x at hk ⊢
      by_cases hx : (x : WCb l) = 0
      · rw [hx]; exact dvd_zero _
      obtain ⟨m, v, v', hv, hv', hvv, hxe⟩ := hfac x x.2 hx
      cases m with
      | zero =>
        exfalso
        apply hk
        refine isUnit_iff_exists_inv.2 ⟨⟨v', hv'⟩, Subtype.ext ?_⟩
        change (x : WCb l) * v' = 1
        rw [hxe, pow_zero, one_mul, hvv]
      | succ m =>
        exact ⟨(l : WCb l) ^ m * v, by rw [hxe, pow_succ]; ring⟩

end GlobalTheory.SmithOE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushout
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_ext {P P' : Obj l R} {a b : Hom P P'} (h : a.f = b.f) : a = b := by
  cases a; cases b; cases h; rfl

theorem comp_assoc {P₁ P₂ P₃ P₄ : Obj l R} (c : Hom P₃ P₄) (b : Hom P₂ P₃) (a : Hom P₁ P₂) :
    (c.comp b).comp a = c.comp (b.comp a) := hom_ext rfl

theorem qmap_comp {P₁ P₂ P₃ : Obj l R} (g : Hom P₂ P₃) (f : Hom P₁ P₂) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem of_isPushout {P : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange @P)
    {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (h : P φ) : P φ' := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  exact hP A B A' B' h

end GlobalTheory.BSP.CoverBC

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem flat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'} {h' : Hom B' C'}
    (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).Flat) (m : ℕ) : (qmap h' m).Flat :=
  of_isPushout RingHom.Flat.isStableUnderBaseChange (H.po m) (hf m)

theorem faithfullyFlat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'}
    {h' : Hom B' C'} (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).FaithfullyFlat) (m : ℕ) :
    (qmap h' m).FaithfullyFlat :=
  of_isPushout RingHom.FaithfullyFlat.isStableUnderBaseChange (H.po m) (hf m)

end GlobalTheory.BSP.CoverBC


open GlobalTheory.BSP.CoverBC in
theorem GlobalTheory.BSP.stable_cover_of_isPO : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R)
    (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'),
    IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  intro l _ R _ B C B' C' h k k' h' H
  have st : Stable h → Stable h' := by
    intro hs
    refine ⟨flat_of_isPO H hs.flat, fun B'' k₂ => ?_⟩
    obtain ⟨C'', k₀, h'', H₂⟩ := hs.po B'' (k₂.comp k)
    have e : k₀.comp h = (h''.comp k₂).comp k := by rw [H₂.comm, comp_assoc]
    obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.T.prismPushoutModAdicPow_universal l R B C B' C' h k k' h' H C'' k₀ (h''.comp k₂) e
    refine ⟨C'', c, h'', ⟨hc₂, fun m => ?_⟩⟩
    have s := H₂.po m
    rw [← hc₁, qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp] at s
    refine IsPushout.of_top s ?_ (H.po m)
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← qmap_comp, ← qmap_comp, hc₂]
  exact ⟨st, fun hc => ⟨st hc.stable, faithfullyFlat_of_isPO H hc.ff⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleDescentFiniteLevel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevH

open CategoryTheory

theorem lev_ring {A B D T : Type} [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B]
    (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T)
    (hff : (algebraMap A B).FaithfullyFlat)
    (hpo1 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q))
    (hpo2 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B)))
      (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂))
    (e1 : q₂₃.comp p = q₁₂.comp q) (e2 : q₂₃.comp q = q₃) (e3 : q₁₃.comp p = q₁₂.comp p) (e4 : q₁₃.comp q = q₃)
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) D) (hε : IsUnit ε) (hc : ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃) :
    ∃ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) ∧
      Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hw : p.comp (algebraMap A B) = q.comp (algebraMap A B) := by
    have := congrArg CommRingCat.Hom.hom hpo1.w
    simpa using this
  have hr : ∀ c, p (algebraMap A B c) = q (algebraMap A B c) := fun c => RingHom.congr_fun hw c
  let N : Submodule A (Fin d → B) :=
    { carrier := {z | (fun i => p (z i)) = ε.mulVec fun i => q (z i)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        have e : (fun i => q ((a + b) i)) = (fun i => q (a i)) + fun i => q (b i) := by
          funext i; simp [map_add (f := _)]
        rw [e, Matrix.mulVec_add, ← ha, ← hb]
        funext i; simp [map_add (f := _)]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
        exact (Matrix.mulVec_zero ε).symm
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        have e1 : (fun i => p ((c • z) i)) = q (algebraMap A B c) • fun i => p (z i) := by
          funext i; simp [Algebra.smul_def, map_mul, hr]
        have e2 : (fun i => q ((c • z) i)) = q (algebraMap A B c) • fun i => q (z i) := by
          funext i; simp [Algebra.smul_def, map_mul]
        rw [e1, e2, Matrix.mulVec_smul, hz] }
  exact ⟨N, fun z => Iff.rfl, _root_.GlobalTheory.descent_free_cocycle A B D T p q q₁₂ q₂₃ q₁₃ q₃ hff hpo1 hpo2 e1 e2 e3 e4 d ε hε hc N
    fun z => Iff.rfl⟩

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_comp_assoc {B C D E : Obj l R} (h : Hom D E) (g : Hom C D) (f : Hom B C) :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem lev_prism [Fact l.Prime] {B C D : Obj l R} (h : Hom B C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (m : ℕ) (d : ℕ) (ε : Matrix (Fin d) (Fin d) D.A) (hε : IsUnit ε)
    (hcoc : ∀ (T : Obj l R) (q₁₂ q₂₃ q₁₃ : Hom D T) (q₃ : Hom C T), q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ →
      q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ε.map q₁₂.f * ε.map q₂₃.f = ε.map q₁₃.f) :
    letI := (qmap h m).toAlgebra
    ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m),
      (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = (ε.map (Ideal.Quotient.mk (adI D ^ m))).mulVec
        fun i => qmap q m (z i)) ∧
      Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧
        IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  let := (qmap h m).toAlgebra
  have c1 : p.comp h = q.comp h := hpo.comm
  refine Exists.elim (hc.stable.po D (p.comp h)) fun T hT => Exists.elim hT fun q₃ hT => Exists.elim hT
    fun q₁₂ hT => ?_
  have c2 : q₃.comp h = q₁₂.comp (p.comp h) := hT.comm
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp q) q₃ (by
      rw [hom_comp_assoc, ← c1, c2])) fun q₂₃ h23 => ?_
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp p) q₃ (by
      rw [hom_comp_assoc, c2])) fun q₁₃ h13 => ?_
  have hpo2 := hT.po m
  have hq : qmap (p.comp h) m = (qmap p m).comp (qmap h m) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  rw [hq] at hpo2
  have hq2 : ∀ (k k' : Hom D T) (k'' : Hom C T), k.comp p = k'.comp q → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap q m) :=
    fun k k' k'' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq3 : ∀ (k : Hom D T) (k' : Hom C T), k.comp q = k' → (qmap k m).comp (qmap q m) = qmap k' m :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq4 : ∀ (k : Hom D T) (k' : Hom D T), k.comp p = k'.comp p → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap p m) :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  refine lev_ring (qmap p m) (qmap q m) (qmap q₁₂ m) (qmap q₂₃ m) (qmap q₁₃ m) (qmap q₃ m) (hc.ff m) (hpo.po m) hpo2
    (hq2 q₂₃ q₁₂ q₃ h23.1.1) (hq3 q₂₃ q₃ h23.1.2) (hq4 q₁₃ q₁₂ h13.1.1) (hq3 q₁₃ q₃ h13.1.2) d _
    (hε.map (Ideal.Quotient.mk (adI D ^ m)).mapMatrix) ?_
  have := congrArg (fun M : Matrix (Fin d) (Fin d) T.A => M.map (Ideal.Quotient.mk (adI T ^ m)))
    (hcoc T q₁₂ q₂₃ q₁₃ q₃ h23.1.1 h23.1.2 h13.1.1 h13.1.2)
  simp only [Matrix.map_mul] at this
  exact this

end GlobalTheory.BSP.LevH

namespace GlobalTheory.BSP.LevH

theorem descent_at_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ m : ℕ, letI := (qmap h m).toAlgebra; ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m), (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ m))).mulVec fun i => qmap q m (z i)) ∧ Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧ IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  intro l _ K bk d S B C D h f p q hc hpo m
  refine lev_prism h p q hc hpo m d (S.ε (p.comp f) (q.comp f))
    ⟨⟨S.ε (p.comp f) (q.comp f), S.ε (q.comp f) (p.comp f), by rw [S.ε_trans, S.ε_refl],
      by rw [S.ε_trans, S.ε_refl]⟩, rfl⟩ ?_
  intro T q₁₂ q₂₃ q₁₃ q₃ e1 e2 e3 e4
  have a1 : q₂₃.comp (p.comp f) = q₁₂.comp (q.comp f) := by rw [← hom_comp_assoc, e1, hom_comp_assoc]
  have a2 : q₂₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e2]
  have a3 : q₁₃.comp (p.comp f) = q₁₂.comp (p.comp f) := by rw [← hom_comp_assoc, e3, hom_comp_assoc]
  have a4 : q₁₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e4]
  rw [S.ε_nat, S.ε_nat, S.ε_nat, a1, a2, a3, a4, S.ε_trans]

end GlobalTheory.BSP.LevH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlace
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem tameAnyFix_map_primeToPart {M K : Type} [Monoid M] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l]
    (ι : M →* K) (x : M) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  have hl : l.Prime := Fact.out
  unfold Formalism.CyclotomicNorms.primeToPart
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0]
    have e : ∀ n : ℕ, n = 0 → (((1 : ℕ) : ZMod n)⁻¹).val = 1 := by
      intro n hn
      subst hn
      rw [Nat.cast_one, ZMod.inv_one]
      rfl
    have e0 : l ^ (Nat.factorization 0) l = 1 := by simp
    rw [e0, e _ (by simp)]
    simp
  · set a := (orderOf x).factorization l with ha
    set m := orderOf x / l ^ a with hm
    have hmul : l ^ a * m = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : Nat.Coprime (l ^ a) m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
    have hmpos : 0 < m := Nat.ordCompl_pos l hpos.ne'
    haveI : NeZero m := ⟨hmpos.ne'⟩
    have h1 : (ι x ^ m) ^ l ^ a = 1 ^ l ^ a := by
      rw [← pow_mul, mul_comm, hmul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
    have h2 : ι x ^ m = 1 := by
      have := iterateFrobenius_inj K l a
      exact this (by simpa [iterateFrobenius_def] using h1)
    have h3 : l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast [ZMod.natCast_zmod_val]
      have := ZMod.coe_mul_inv_eq_one (l ^ a) hcop
      simpa using this
    rw [map_pow]
    have h4 : ι x ^ (l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val) = ι x ^ 1 := by
      rw [pow_eq_pow_mod _ h2, h3, ← pow_eq_pow_mod _ h2]
    rw [h4, pow_one]

theorem tameAnyFix_isoLoc (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem tameAnyFix_not_over (D : D7) (i : D.nd.Loc) (k : Fin 2) (h : D.nd.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
  intro hl
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hl' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := hl
  have hc : Nat.Coprime (D.nd.l i) (D.host.g k) := (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 h
  have hc' : IsCoprime ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hc
  obtain ⟨a, b, hab⟩ := hc'
  apply (D.naut.plGw k v).isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ hg)

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAway
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem charpoly_redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (s : G D.host.E D.nd.Om) :
    Matrix.charpoly ((redF D i ρ s : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem teich_pow_sub_one_eq_ED_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ε c hε hc
  have hd : ED K t ϖ = toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) := by
    rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨⟨ξ, hξ, hμ⟩, -, hθδ, -⟩ := (GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)
  set G : Ainf l := ∑ i ∈ Finset.range c, WittVector.teichmuller l ε ^ i with hG
  set w : Ainf l := (v : Ainf l) * (muOf δ * G) with hwdef
  have hkey : WittVector.teichmuller l ε ^ c - 1 = ϖ.ev a (eis l a e) * w := by
    have h1 : WittVector.teichmuller l ε ^ c - 1 = muOf ε * G := by
      rw [muOf, hG, mul_comm, geom_sum_mul]
    rw [h1, hμ, ← hv, hwdef]
    ring
  have hθG : ((Per.θ l G : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hG, map_sum]
    simp only [map_pow, WittVector.fontaineTheta_teichmuller, hε.1, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  have hθw : ((Per.θ l w : Per.OC l) : ℂ_[l]) ≠ 0 := by
    have h1 : ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
      (v.isUnit.map (Per.θ l)).ne_zero (Subtype.ext (h.trans rfl))
    have h2 : ((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h => hθδ (Subtype.ext (h.trans rfl))
    have h3 : (c : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc
    have h4 : ((Per.θ l w : Per.OC l) : ℂ_[l]) =
        ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) * (((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) *
          ((Per.θ l G : Per.OC l) : ℂ_[l])) := by
      rw [hwdef, map_mul, map_mul]
      rfl
    rw [h4, hθG]
    exact mul_ne_zero h1 (mul_ne_zero h2 h3)
  have hwu : IsUnit (ainfToBdRp l w) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
    change Per.θD l (GlobalTheory.MemLoc.aDp l w) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact hθw)
  refine ⟨toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O), ?_, ?_⟩
  · have h2 : toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O) =
        (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O) (ainfToBdRp l w) := by
      simp [toOD]
    rw [h2]
    exact hwu.map _
  · have h3 : ((1 : O) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ε : OA l O) ^ c - 1 =
        ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) * ((1 : O) ⊗ₜ[ℤ_[l]] w) := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hkey,
        Algebra.TensorProduct.one_def, TensorProduct.tmul_sub]
    rw [hd, ← map_mul, ← h3, map_sub, map_pow, map_one]

end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_image_deRham_plus_component_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → ∃ Ψ : ↥(W.N T) → T.V ⊗[ℚ_[l]] (D.loc l).R.BdR, (∀ x, Ψ x ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0) ∧ (∀ z ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → (D.loc l).R.BdR) (x : Fin m → ↥(W.N T)), (∀ j, b j ∈ ((D.loc l).PD K).Fil 0) ∧ z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι) ∧ ∀ (x : ↥(W.N T)) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex C h T i ζ x r = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS (D.loc l) s ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (tS (D.loc l) s ^ r) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T i ζ x ((r : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.NL.PerS.image | exact GlobalTheory.NL.PerS.image | (intros; apply GlobalTheory.NL.PerS.image <;> assumption)
end

