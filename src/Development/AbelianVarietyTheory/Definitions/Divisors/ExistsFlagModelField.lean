module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015

@[expose] public section

noncomputable section

namespace GlobalTheory.FlagMod.LowRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

section Alg

theorem initSpan_low {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} (hm : m ≤ 1) {v v' : Fin m → N}
    (h : initSpan R v m = initSpan R v' m) (i : ℕ) : initSpan R v i = initSpan R v' i := by
  rcases i with _ | i
  · simp [initSpan]
  · have e : {j : Fin m | (j : ℕ) < i + 1} = {j : Fin m | (j : ℕ) < m} := by
      ext j; have := j.2; simp only [Set.mem_ofPred_eq]; omega
    unfold initSpan at h ⊢
    rw [e, h]

end Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Red

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem initSpan_frVec_top {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (M : MChart Y)
    (h : ⊤ ≤ (frX P ≫ Y.j) ⁻¹ᵁ M.U) (σ : E →+* ℂ) :
    initSpan S (frVec Y P rfl σ) (Dw.mult σ) = eigLie c (frX P ≫ Y.j) σ := by
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev _ M.U h) (frX P) (frX_snd P)
    (spMap_ev _ M.hU h).symm
  let Λ : M.Lift (ev _ M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have hv : ∀ j, Λ.Vec ((vec M _ h).symm (frVec Y P rfl σ j)) (P.u σ j) := fun j =>
    (vec_iff_toModel h Λ eΛ (frX_fst P) rfl _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M S _ P.x Λ σ
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M S _ P.x Λ
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv' => ?_
  · rintro _ ⟨j, -, rfl⟩
    rw [← (vec M _ h).apply_symm_apply (frVec Y P rfl σ j)]
    exact (vec_mem_eigLie M _ h σ _).2 ((heig _ _ (hv j)).1 (P.eig σ j))
  · obtain ⟨cv, rfl⟩ := (vec M _ h).surjective v
    obtain ⟨w, hw⟩ := (hex cv).exists
    obtain ⟨a, ha⟩ := (P.basis σ w (htan cv w hw) ((heig cv w hw).2 ((vec_mem_eigLie M _ h σ _).1 hv'))).exists
    have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _ _ (P.u σ) a w hv).1 ha
    refine mem_initSpan.2 ⟨a, fun j hj => absurd j.2 (not_lt.2 hj), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (hco w (htan cv w hw)).unique h4 hw, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]

def ofFrames (hm : ∀ σ, Dw.mult σ ≤ 1) (F : Frames Y (𝟙 Y.X)) (hF : F.TopEigen) : FlagModel Y where
  YY := Y.X
  π := 𝟙 _
  proper := inferInstance
  normal := Y.normal
  flat := by rw [Category.id_comp]; exact Y.flat
  F := F
  dense := by
    have : IsIso (genMap (Y := Y) (𝟙 Y.X)) :=
      ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [Category.id_comp, pullback.condition]),
        by apply pullback.hom_ext <;> simp only [genMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp],
        by apply pullback.hom_ext <;> simp only [genMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp]⟩
    exact Y.jQ_dense.preimage (genMap (Y := Y) (𝟙 Y.X)).homeomorph.isOpenMap
  top := hF
  rep S _ _ P := by
    refine ⟨frX P ≫ Y.j, ⟨Category.comp_id _, fun S' _ _ ψ P' hP k z' ez hz hx σ i => ?_⟩,
      fun z hz => (Category.comp_id _).symm.trans hz.1⟩
    refine initSpan_low (hm σ) ?_ i
    rw [hF S' _ (frX_snd P') z' hx k hz σ]
    exact initSpan_frVec_top P' _ (F.inM hz hx) σ
  fin K _ _ z := (Set.finite_singleton z).subset fun z' ⟨hx, _⟩ => by simpa using hx

end Red

section Frames

variable {O : Type} [CommRing O] {β : O →+* c.F}

structure Proj (β : O →+* c.F) where
  m : (E →+* ℂ) → ℕ
  a : ∀ σ, Fin (m σ) → 𝓞 E
  κ : ∀ σ, Fin (m σ) → O
  spec : ∀ σ (R : Type) [CommRing R] [Algebra c.F R] (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R),
    (∀ b : 𝓞 E, ρ b * (∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)) =
      algebraMap c.F R (embK c σ b) • ∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)) ∧
    ∀ x : Fin n → R, (∀ b : 𝓞 E, (ρ b).mulVec x = algebraMap c.F R (embK c σ b) • x) →
      (∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)).mulVec x = x

theorem nonempty_proj_id : Nonempty (Proj (RingHom.id c.F)) := by
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose m a κ h using GlobalTheory.exists_eigen_projector_ringOfIntegers E c.F (embF c) hemb
  exact ⟨⟨m, a, κ, h⟩⟩

variable {Y : Model Xo c β} {S : Type} [CommRing S]

def str (x : Sp S ⟶ Y.X) : O →+* S := (ev (x ≫ Y.s) ⊤ le_top).comp (toΓ O)

theorem str_eq {x : Sp S ⟶ Y.X} {g : O →+* S} (h : x ≫ Y.s = spMap g) : str x = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_ev_top _).trans h))

theorem ev_str (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (o : O) :
    ev x M.U h (str (tau M.hU) o) = str x o := by
  have : str x = (ev x M.U h).comp (str (tau M.hU)) := str_eq (by
    rw [← spMap_comp', str, spMap_ev_top, ← Category.assoc]
    exact congrArg (· ≫ Y.s) (spMap_ev x M.hU h).symm)
  rw [this]; rfl

theorem str_gen [Algebra c.F S] {y : Sp S ⟶ Xo.XF c} (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (o : O) :
    str (y ≫ Y.j) o = algebraMap c.F S (β o) := by
  rw [str_eq (g := (algebraMap c.F S).comp β) (by
    rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hy, spMap_comp'])]
  rfl

variable (p : Proj β)

def pm (M : MChart Y) (σ : E →+* ℂ) : Matrix (Fin M.n) (Fin M.n) Γ(Y.X, M.U) :=
  ∑ k, str (tau M.hU) (p.κ σ k) • M.ρ (p.a σ k)

theorem pm_map (M : MChart Y) (σ : E →+* ℂ) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) :
    (pm p M σ).map (ev x M.U h) = ∑ k, str x (p.κ σ k) • (M.ρ (p.a σ k)).map (ev x M.U h) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pm, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, ev_str]

theorem vec_pm (M : MChart Y) (σ : E →+* ℂ) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (cv : Fin M.n → S) :
    vec M x h (((pm p M σ).map (ev x M.U h)).mulVec cv) =
      ∑ k, str x (p.κ σ k) • actR Y.t.act (p.a σ k) (vec M x h cv) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pm_map, Matrix.sum_mulVec, map_sum]
  simp only [Matrix.smul_mulVec, map_smul, actR_vec]

theorem pm_gen [Algebra c.F S] (M : MChart Y) (σ : E →+* ℂ) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U) :
    (∀ cv, M.Eig (ev _ M.U h) σ cv ↔ ((pm p M σ).map (ev _ M.U h)).mulVec cv = cv) ∧
      (pm p M σ).map (ev _ M.U h) * (pm p M σ).map (ev _ M.U h) = (pm p M σ).map (ev _ M.U h) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  obtain ⟨h1, h2⟩ := p.spec σ S M.n ((ev _ M.U h).mapMatrix.comp ρ)
  simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, hρ, ← str_gen (Y := Y) hy, ← pm_map] at h1 h2
  refine ⟨fun cv => ⟨h2 cv, fun hx b => ?_⟩, ?_⟩
  · have := congrArg (fun A => Matrix.mulVec A cv) (h1 b)
    simpa only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx] using this
  · ext i j
    have := h2 (fun k => (pm p M σ).map (ev _ M.U h) k j) (fun b => by
      funext k
      exact congrFun (congrFun (h1 b) k) j)
    exact congrFun this i

def GenIn (Y : Model Xo c β) : Prop :=
  ∀ M : MChart Y, ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (y : Sp L ⟶ Xo.XF c)
    (h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U), y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧
      Function.Injective (ev (y ≫ Y.j) M.U h)


variable (Y) in
structure ECh where
  M : GChart Y
  V : Y.X.Opens
  le : V ≤ M.U
  u : ∀ σ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult σ)) Γ(Y.X, V)
  w : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin M.n) Γ(Y.X, V)
  wu : ∀ σ, w σ * u σ = 1
  uw : ∀ σ, u σ * w σ = (pm p M.toMChart σ).map (resG Y.X le)

variable {p}

theorem ECh.fix_iff (k : ECh Y p) (σ : E →+* ℂ) (z : Sp S ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ k.V) (h : ⊤ ≤ z ⁻¹ᵁ k.M.U)
    (cv : Fin k.M.n → S) : ((pm p k.M.toMChart σ).map (ev z _ h)).mulVec cv = cv ↔
      ∃ a, ((k.u σ).map (ev z _ hz)).mulVec a = cv := by
  have e : (pm p k.M.toMChart σ).map (ev z _ h) = (k.u σ).map (ev z _ hz) * (k.w σ).map (ev z _ hz) := by
    rw [← Matrix.map_mul, k.uw]
    ext i j
    exact (ev_res z _ hz h _).symm
  rw [e, ← Matrix.mulVec_mulVec]
  refine ⟨fun h => ⟨_, h⟩, ?_⟩
  rintro ⟨a, rfl⟩
  rw [Matrix.mulVec_mulVec (M := (k.w σ).map _), ← Matrix.map_mul, k.wu, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mulVec]


end Frames

section Gen

theorem exists_field (A : Type) [CommRing A] [IsDomain A] :
    ∃ (L : Type) (_ : Field L) (f : A →+* L), Function.Injective f :=
  ⟨FractionRing A, inferInstance, algebraMap _ _, IsFractionRing.injective _ _⟩

theorem genIn_of {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    (h : ∀ (M : MChart Y) (L : Type) [Field L] (f : Γ(Y.X, M.U) →+* L), Function.Injective f →
      ∃ (_ : Algebra c.F L) (y : Sp L ⟶ Xo.XF c),
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ y ≫ Y.j = spMap f ≫ tau M.hU) :
    GenIn Y := fun M => by
  have := M.dom
  obtain ⟨L, _, f, hf⟩ := exists_field Γ(Y.X, M.U)
  obtain ⟨A, y, h1, h2⟩ := h M L f hf
  have hU : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U := h2 ▸ le_preimage_comp _ (tau_le M.hU le_rfl)
  refine ⟨L, inferInstance, A, y, hU, h1, ?_⟩
  rw [ev_congr h2 _ _ (h2 ▸ hU), ev_spMap_tau]
  exact hf

theorem spec_generic {A L : Type} [CommRing A] [Field L] (f : A →+* L) (hf : Function.Injective f)
    (q : PrimeSpectrum L) (t : PrimeSpectrum A) : PrimeSpectrum.comap f q ⤳ t := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  show Ideal.comap f ⊥ ≤ _
  rw [Ideal.comap_bot_of_injective _ hf]
  exact bot_le

theorem genIn_id (Y : Model Xo c (RingHom.id c.F)) : GenIn Y := genIn_of fun M L _ f hi => by
  have := M.dom
  have := Y.jQ_open
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  have hd : Dense (Set.range Y.j) := by
    have := (pullback.fst Y.s (spMap (RingHom.id c.F))).homeomorph.surjective.denseRange.comp Y.jQ_dense
      (pullback.fst Y.s (spMap (RingHom.id c.F))).homeomorph.continuous
    refine this.mono ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, Scheme.Hom.comp_apply _ _ _⟩
  let z : Sp L ⟶ Y.X := spMap f ≫ tau M.hU
  have hr : Set.range z ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hd.inter_open_nonempty (Set.range (tau M.hU))
      M.hU.fromSpec.isOpenEmbedding.isOpen_range ⟨_, (⊥ : PrimeSpectrum Γ(Y.X, M.U)), rfl⟩
    have hs : spMap f q ⤳ t := spec_generic f hi q t
    rw [Scheme.Hom.comp_apply]
    exact (hs.map (tau M.hU).continuous).mem_open Y.j.isOpenEmbedding.isOpen_range ht
  let A : Algebra c.F L := (str z).toAlgebra
  refine ⟨A, IsOpenImmersion.lift Y.j z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have e : Y.j ≫ Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over,
      show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact (spMap_ev_top _).symm

end Gen

end GlobalTheory.FlagMod.LowRank
