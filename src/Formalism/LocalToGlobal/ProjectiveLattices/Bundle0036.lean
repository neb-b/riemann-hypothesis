module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AdelicContinuousOfUniform
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp



end BC

section Loc

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Loc

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def evCAlg (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z where
  toFun := evC hG Z
  map_one' := evalAt_one _ _ (genFr hG Z) (hT Z)
  map_mul' f g := evalAt_mul _ _ f g (genFr hG Z)
  map_zero' := evalAt_zero _ _ (genFr hG Z)
  map_add' f g := evalAt_add _ _ f g (genFr hG Z)
  commutes' a := by
    show evC hG Z (algebraMap c.F (Rul Xo c) a) = algebraMap c.F (Om Z) a
    rw [Algebra.algebraMap_eq_smul_one]
    show evalAt _ _ (a • (1 : Rul Xo c)) (genFr hG Z) = _
    rw [evalAt_smul, evalAt_one _ _ _ (hT Z), mul_one]

lemma evCAlg_apply (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) (f : Rul Xo c) :
    evCAlg hG hT Z f = evC hG Z f := rfl

end Gen

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

abbrev RZ : Type := Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω)

def rzMap : Rp X la N →ₐ[Kp X la N] RZ X la N Ω :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)

lemma rzMap_emb (F : X.Forms) :
    rzMap X la N Ω gF (emb X la N F) = (1 : Kp X la N) ⊗ₜ ((1 : X.Kl la) ⊗ₜ gF F) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)
      ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rfl

variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev RZs : Type := Localization.Away (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))

def lwZ : Lw X la w →+* RZs X la N Ω gF w :=
  Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)

lemma lwZ_alg (r : Rp X la N) :
    lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) r) =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF r) := by
  show (Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))
      (algebraMap (Rp X la N) (Localization.Away (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) r) = _
  exact IsLocalization.map_eq _ _

def phiZ : ↥(Frac0 X la w) →ₐ[Kp X la N] RZs X la N Ω gF w where
  toRingHom := (lwZ X la N Ω gF w).comp (Frac0 X la w).val.toRingHom
  commutes' k := by
    show lwZ X la N Ω gF w (algebraMap (Kp X la N) (Lw X la w) k) = _
    rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), lwZ_alg, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]

lemma phiZ_apply (x : ↥(Frac0 X la w)) : phiZ X la N Ω gF w x = lwZ X la N Ω gF w (x : Lw X la w) := rfl

end Rec

section Inst

variable {D : D7} {T : Top D} (j : ℕ)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (Z : Comp (T.Q.Xo j) T.Q.c)

def formsEvR : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] Om Z :=
  AddMonoidAlgebra.liftNCAlgHom (evCAlg hG hT Z) 1 (fun _ _ => Commute.all _ _)

lemma formsEvR_single (d : Deg D j) (f : T.R j) :
    formsEvR j hG hT Z (AddMonoidAlgebra.single d f) = evC hG Z f := by
  show AddMonoidAlgebra.liftNC (evCAlg hG hT Z).toRingHom.toAddMonoidHom
      ((1 : Multiplicative (Deg D j) →* Om Z) : Multiplicative (Deg D j) → Om Z) (AddMonoidAlgebra.single d f) = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp [evCAlg_apply]

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.EtArchPf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Torus

open ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def thRat (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Fin X.r → Vsp X.dim) : ℝ :=
  ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)






end Torus

variable {D : D7} {T : Top D} (h : LawsP T)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PerFr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_add {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (v + w) = Data.emb σ v + Data.emb σ w := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_add _ _ _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [Matrix.mulVec_add]; done)
    | (simp [hermC, Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)])

theorem perFr_zero {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x 0 τ i = 0 := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (0 : Fin r → E) = 0 := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_zero _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [hermC]; done)
    | (unfold hermC; simp)

end PerFr

section Lin

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : Fin g → ℂ :=
  Pi.single (e.symm ⟨τ, i⟩) 1

theorem eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (q : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eb e τ i (e.symm q) = if q = ⟨τ, i⟩ then 1 else 0 := by
  by_cases hq : q = ⟨τ, i⟩
  · subst hq
    simp [eb]
  · simp [eb, hq, Pi.single_apply, e.symm.injective.eq_iff]

theorem sum_eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ)
    (c : Fin (Dw.mult τ) → ℂ) (l : Fin (Dw.mult τ)) : (∑ j, c j • eb e τ j) (e.symm ⟨τ, l⟩) = c l := by
  simp [Finset.sum_apply, eb_apply]

end Lin

section Der

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} {e1 e2 : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e2 (h z) = e1 z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hv : IsDerivAt0 e1 w v) : IsDerivAt0 e2 (h w) v := by
  unfold IsDerivAt0 at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have h0 : h 0 = 0 := map_zero h
  have h3 : e2 0 = e1 0 := by simpa [h0] using he 0
  refine ⟨h1.trans h3.symm, ?_⟩
  intro U hU f
  refine (h2 U hU f).trans ?_
  have hfun : (fun z => valAt' (e1 z) U f) =
      (fun y => valAt' (e2 y) U f) ∘ (LinearEquiv.toContinuousLinearEquiv h) := by
    funext z
    simp [he]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp [h0]

end Der

section Fam

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def pmOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) where
  toFun a := fun j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  map_zero' := by
    funext j
    simp [perFr_zero]
  map_add' a b := by
    funext j
    simp [perFr_add]

def ExpUniq {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P P' : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P' →
    ∀ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b, gam a = a + l.M • b) →
      (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, P' (gam a) = h (P a)) →
      ∀ z, (F.ex i P' (h z)).left = (F.ex i P z).left

def ExpLin {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (m : ℕ) (w : Fin m → (Fin g → ℂ)) (vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
      (cf : Fin m → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) →
      IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v → IsCombAt (F.u i P) vs cf v

def ExpTan {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (w : Fin g → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      IsDerivAt0 (fun z => (F.ex i P z).left) w v →
      IsTanAt (F.u i P) v ∧ ∀ j, w = Pi.single j 1 → IsEigAt c (e j).1 v

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}

theorem derivAt_exists {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left, IsDerivAt0 (fun z => (F.ex i P z).left) w v := by
  obtain ⟨v, hv, -⟩ := (F.ex_diff i P hP).1 w
  exact ⟨_, hv⟩

end Fam

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Main

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PtOfSInst
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

def PtOfSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  0 < wL.n → ∀ (L : Type) [Field L] [Algebra (Kp (recPlus h j hj) la G.N) L]
    (φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] L),
    ∃ (alg : T.Q.c.F →+* L) (y : letI := alg.toAlgebra; FrPt (T.Q.Xo j) T.Q.c L),
      (letI := alg.toAlgebra; ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (ψ : Om Z →ₐ[T.Q.c.F] L), FrMap ψ (genFr hG Z) y) ∧
      (∀ a : T.Q.c.F, alg a = algebraMap (Kp (recPlus h j hj) la G.N) L
        (@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)
          (algebraMap T.Q.c.F ((recPlus h j hj).Kl la) a))) ∧
      letI := alg.toAlgebra
      (∑ k, algebraMap (Kp (recPlus h j hj) la G.N) L
          (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
          evR (T.Q.Xo j) T.Q.c ((G.w k : T.R j)) y) ≠ 0 ∧
      ∀ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL k)),
        φ (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
          ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ g), emb_mem_Vw (recPlus h j hj) la G.N _ g⟩)) =
        evR (T.Q.Xo j) T.Q.c ((g : T.R j)) y /
          (∑ k', algebraMap (Kp (recPlus h j hj) la G.N) L
            (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k'))) *
            evR (T.Q.Xo j) T.Q.c ((G.w k' : T.R j)) y) ^ k

end Formalism.L2.Pj
end
end

