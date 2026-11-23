module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.ChgBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ :=
  RingHom.ext fun a => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem isCombAt_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {v' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, v' j = spMap (dualMap φ) ≫ v j)
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} {w' : Sp (DualNumber T) ⟶ Xo.univ.t.G.left}
    (hw : w' = spMap (dualMap φ) ≫ w) (h : IsCombAt x v cf w) : IsCombAt x' v' (fun j => φ (cf j)) w' := by
  obtain ⟨u, hu, hprod⟩ := h
  let D : tEps x' ⟶ tEps x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap T (DualNumber T)) ≫ x'
    rw [hx, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_alg])
  have hL : ∀ L : List (tEps x ⟶ Xo.univ.t.G), (L.map (D ≫ ·)).prod = D ≫ L.prod := by
    intro L
    induction L with
    | nil => simp [MonObj.comp_one]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.comp_mul]
  refine ⟨fun j => D ≫ u j, fun j => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u j).left = spMap (epsMul (φ (cf j))) ≫ v' j
    rw [hu j, hv j, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_eps]
  · have e : (List.ofFn fun j => D ≫ u j) = (List.ofFn u).map (D ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, hL, Over.comp_left, hprod, hw]
    rfl

theorem isCombAt_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  obtain ⟨u, hu, hprod⟩ := h
  obtain ⟨u', hu', hprod'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← hprod, ← hprod', e]

theorem ppx_le_cov {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem scal_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem can_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) :
    ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ := by
  let pm : Gx x' ⟶ Gx x :=
    pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition)
  exact ⟨pm, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem gx_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Z : Scheme.{0}} {p q : Z ⟶ Gx x}
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem square {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {y y' : Sp S ⟶ Xo.X}
    {z z' : Sp T ⟶ Xo.X} (pmA : Gx z ⟶ Gx y) (pmB : Gx z' ⟶ Gx y') (pmC : Gx y' ⟶ Gx y) (pm : Gx z' ⟶ Gx z)
    (hsA : pmA ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk z) Xo.univ.t.G).left)
    (hfA : pmA ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk z) Xo.univ.t.G).left ≫ spMap φ)
    (hsB : pmB ≫ (snd (Over.mk y') Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hfB : pmB ≫ (fst (Over.mk y') Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap φ)
    (hsC : pmC ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk y') Xo.univ.t.G).left)
    (hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left ≫ spMap (RingHom.id S))
    (hs : pm ≫ (snd (Over.mk z) Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap (RingHom.id T))
    (sy : LB.Sec (PPx y)) (sy' : LB.Sec (PPx y')) (sz : LB.Sec (PPx z))
    (haA : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z).U i ≤ pmA ⁻¹ᵁ (PPx y).U i),
      (pmA.appLE _ _ h).hom (sy.f i) = sz.f i)
    (haC : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y').U i ≤ pmC ⁻¹ᵁ (PPx y).U i),
      (pmC.appLE _ _ h).hom (scal y a i * sy.f i) = sy'.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z').U i ≤ pm ⁻¹ᵁ (PPx z).U i)
    (hB : (PPx z').U i ≤ pmB ⁻¹ᵁ (PPx y').U i) :
    (pm.appLE _ _ h).hom (scal z (φ a) i * sz.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
  rw [spMap_id] at hfC hf
  replace hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left :=
    hfC.trans (Category.comp_id _)
  replace hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left :=
    hf.trans (Category.comp_id _)
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply gx_ext
    · rw [Category.assoc, hsA, hs, Category.assoc, hsC, hsB]
    · rw [Category.assoc, hfA, Category.assoc, hfC]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap φ) hf)).trans hfB.symm
  have hA := ppx_le_cov pmA hsA i
  have hC := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z' ⟶ Gx y), q = pmB ≫ pmC → ∀ hh : (PPx z').U i ≤ q ⁻¹ᵁ (PPx y).U i,
      (q.appLE _ _ hh).hom (scal y a i * sy.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC ≫ pmB.appLE _ _ hB :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC hB).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC]
  rw [← haA i hA, ← scal_pull φ pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y a i * sy.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frChg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y y' z z' g a hb hz
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  constructor
  · rintro ⟨hx2, hu2, pmB, hsB, hfB, haB⟩
    have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
    refine ⟨hxz, fun τ i => isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) (hcomb τ i), ?_⟩
    obtain ⟨pm, hs, hf⟩ := can_exists (RingHom.id T) (x := z.x) (x' := z'.x)
      (by rw [spMap_id, Category.id_comp, hxz])
    refine ⟨pm, hs, hf, fun i h => ?_⟩
    have hB := ppx_le_cov pmB hsB i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).trans
      (haB i hB)
  · rintro ⟨hxz, hc2, pm, hs, hf, ha⟩
    have hx2 : z'.x = spMap φ.toRingHom ≫ y'.x := by rw [hxz, hx1, hx]
    refine ⟨hx2, fun τ i => isCombAt_unique (hc2 τ i)
      (isCombAt_pull φ.toRingHom hx1 (hu1 τ) rfl (hcomb τ i)), ?_⟩
    obtain ⟨pmB, hsB, hfB⟩ := can_exists φ.toRingHom hx2
    refine ⟨pmB, hsB, hfB, fun i hB => ?_⟩
    have h := ppx_le_cov pm hs i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).symm.trans
      (ha i h)

end GlobalTheory.Frames.ChgBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModelBaseTrivModels
section
noncomputable section

namespace GlobalTheory.PeriodRowsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem isTypeFn_letters (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := fun τ => by
    have hval : relab c σ τ (H.rt : E) = σ ⟨τ (H.rt : E), c.conj τ _⟩ := rfl
    rw [hval]
    refine ⟨fun h => congrArg Subtype.val (σ.injective (h.trans hσ0.symm)), fun h => ?_⟩
    exact (congrArg σ (Subtype.ext h)).trans hσ0
  intro τ
  obtain ⟨τ₀, rfl⟩ := Finite.injective_iff_surjective.1 hinj τ
  have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
    have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
      Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
    have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    rw [Nat.card_congr (e1.trans (e2.trans (Equiv.sigmaSubtype τ₀))), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    exact if_pos ((hrel τ₀).1 h)
  · rw [hcard]
    exact if_neg (fun h' => h ((hrel τ₀).2 h'))

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}

end GlobalTheory.PeriodRowsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliPointFromFgSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem point_from_fg_subalgebra {K F : Type} [CommRing K] [CommRing F] (φ : K →+* F) {X : Scheme.{0}}
    (s : X ⟶ Sp K) [LocallyOfFinitePresentation s] (S : Type) [CommRing S] [Algebra F S] (x : Sp S ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap F S).comp φ)) :
    ∃ S₀ : Subalgebra F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ X, x₀ ≫ s = spMap ((algebraMap F S₀).comp φ) ∧
      spMap S₀.val.toRingHom ≫ x₀ = x := by
  classical
  let P : Finset S ⥤ CommRingCat.{0} :=
    { obj t := .of (Algebra.adjoin F (t : Set S))
      map {t t'} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cP : Cocone P :=
    { pt := .of S
      «ι» := { app t := CommRingCat.ofHom (Algebra.adjoin F (t : Set S)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcP : IsColimit cP := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : S := x
        exact ⟨({x'} : Finset S), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin F (({x'} : Finset S) : Set S)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset S)ᵒᵖ ⥤ Scheme.{0} := P.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cP.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcP.op
  let κ (t : (Finset S)ᵒᵖ) : G.obj t ⟶ Sp K :=
    spMap ((algebraMap F (Algebra.adjoin F (t.unop : Set S))).comp φ)
  have hι {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : G.map f ≫ κ t' = κ t := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (t : (Finset S)ᵒᵖ) : cG.π.app t ≫ κ t = spMap ((algebraMap F S).comp φ) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hG (t : (Finset S)ᵒᵖ) : IsAffine (G.obj t) := inferInstanceAs (IsAffine (Spec _))
  have hGa {t t' : (Finset S)ᵒᵖ} (f : t ⟶ t') : IsAffineHom (G.map f) := inferInstance
  obtain ⟨i, y₀, hy₀, hy₁⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    ({ app := κ, naturality := fun t t' f => (hι f).trans (Category.comp_id _).symm } :
      G ⟶ (Functor.const _).obj (Sp K)) s cG hcG x
    (NatTrans.ext (funext fun t => (hι' t).trans hx.symm))
  exact ⟨Algebra.adjoin F (i.unop : Set S), ⟨i.unop, rfl⟩, y₀, hy₁, hy₀⟩

theorem moduli_point_from_fg_subalgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∃ S₀ : Subalgebra c.F S, S₀.FG ∧ ∃ x₀ : Sp S₀ ⟶ Xo.X, x₀ ≫ Xo.s = sOf c S₀ ∧ spMap S₀.val.toRingHom ≫ x₀ = x := by
  intro E _ _ _ H Dw l Xo c S _ _ x hx
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  exact point_from_fg_subalgebra (IntermediateField.inclusion c.le).toRingHom Xo.s S x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.SecCalc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a * b))) = _
  rw [map_mul, map_mul, map_mul]
  rfl

theorem scal_add' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a + b) i = scal x a i + scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a + b))) = _
  rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  rfl

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S 1)) = _
  rw [map_one, map_one, map_one]

theorem ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (Formalism.L2.PjFree.gxFst (x)) = (Formalism.L2.PjFree.gxFst (x')))
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  dsimp only [Formalism.L2.PjFree.gxFst] at e
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem scal_pull' {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (Formalism.L2.PjFree.gxSnd (x)) = (Formalism.L2.PjFree.gxSnd (x')) ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem pm_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Y : Scheme.{0}} (p q : Y ⟶ Gx x)
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem pm_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) : ∃ pm : Gx x' ⟶ Gx x,
      pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ :=
  ⟨pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem secBC_iff {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) :
    SecBC φ a x x' s s' ↔ ∀ i : Fin 1 → Xo.univ.t.PP.L.ι,
      s'.f i = scal x' (φ a) i * (pm.appLE _ _ (ppx_le pm hs i)).hom (s.f i) := by
  constructor
  · rintro ⟨q, qs, qf, ha⟩ i
    obtain rfl : q = pm := pm_ext _ _ (qs.trans hs.symm) (qf.trans hf.symm)
    rw [← ha i (ppx_le q hs i), map_mul, scal_pull' φ q hf]
  · intro h
    refine ⟨pm, hs, hf, fun i hi => ?_⟩
    rw [h i, map_mul, scal_pull' φ pm hf]

theorem sec_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  intro E _ _ _ H Dw l Xo S T U _ _ _ φ ψ x x' x'' hx hx'
  obtain ⟨p, ps, pf⟩ := pm_exists φ hx
  obtain ⟨q, qs, qf⟩ := pm_exists ψ hx'
  refine ⟨fun a s s' s'' h => ?_, fun a s t => ?_, fun a s s' t' h => ?_,
    fun a b i => ⟨scal_mul' x a b i, scal_add' x a b i, scal_one' x i⟩⟩
  · have rs : (q ≫ p) ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x'') Xo.univ.t.G).left := by
      rw [Category.assoc, ps, qs]
    have rf : (q ≫ p) ≫ (fst (Over.mk x) Xo.univ.t.G).left =
        (fst (Over.mk x'') Xo.univ.t.G).left ≫ spMap (ψ.comp φ) := by
      rw [Category.assoc, pf, ← Category.assoc, qf, Category.assoc, spMap_comp']
    rw [secBC_iff φ a p ps pf] at h
    rw [secBC_iff ψ 1 q qs qf, secBC_iff (ψ.comp φ) a (q ≫ p) rs rf]
    refine forall_congr' fun i => ?_
    have e : (q ≫ p).appLE _ _ (ppx_le (q ≫ p) rs i) = p.appLE _ _ (ppx_le p ps i) ≫ q.appLE _ _ (ppx_le q qs i) :=
      (Scheme.Hom.appLE_comp_appLE q p _ _ _ _ _).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, h i, map_one, scal_one' x'' i, _root_.one_mul, map_mul,
      scal_pull' ψ q qf]
    rfl
  · rw [secBC_iff (RingHom.id S) a (𝟙 (Gx x)) (Category.id_comp _)
      (by rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm)]
    refine forall_congr' fun i => ?_
    have e : ∀ hh : (PPx x).U i ≤ (𝟙 (Gx x) : Gx x ⟶ Gx x) ⁻¹ᵁ (PPx x).U i,
        (𝟙 (Gx x) : Gx x ⟶ Gx x).appLE _ _ hh = 𝟙 _ := by
      intro hh
      exact (Scheme.Hom.appLE_eq_app (𝟙 (Gx x) : Gx x ⟶ Gx x)).trans (Scheme.Hom.id_app _)
    rw [e]
    rfl
  · rw [secBC_iff φ 1 p ps pf] at h
    rw [secBC_iff φ a p ps pf]
    refine forall_congr' fun i => ?_
    rw [h i, map_one, scal_one' x' i, _root_.one_mul]

end GlobalTheory.Frames.SecCalc
end
end

