module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCover
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
theorem _root_.GlobalTheory.Frames.exists_univFrame_testRing : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (p : _root_.Formalism.L2.Pj.TRing c.F) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c p.R),
    ∃ (A : _root_.Formalism.L2.Pj.TRing c.F) (π : p.R →ₐ[c.F] A.R)
      (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ)
      (u : _root_.Formalism.L2.Pj.FrPt Xo c A.R), _root_.GlobalTheory.Frames.UnivFrame y₀ π X s u := by
  intro hbc E _ _ _ H Dw l Xo c p y₀
  obtain ⟨A, π, X, s, h⟩ := _root_.GlobalTheory.exists_frameRing_testRing c.F (E →+* ℂ) Dw.mult p
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hbc E H Dw l Xo c p.R A.R π y₀
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R u₀ X s h.1
  exact ⟨A, π, X, s, u, h, u₀, hu₀, hu⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
section
namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unit_form_inv {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    ∑ a, ∑ b, (g *ᵥ x) a * J b a * σ ((g *ᵥ y) b) = ∑ a, ∑ b, x a * J b a * σ (y b) := by
  have key : ∀ (u v : Fin n → A), ∑ a, ∑ b, u a * J b a * σ (v b) = (σ ∘ v) ⬝ᵥ (J *ᵥ u) := by
    intro u v
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : σ ∘ (g *ᵥ y) = (σ ∘ y) ᵥ* Formalism.UG.cT σ g := by
    funext b
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [key, key, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem unit_det_norm {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hJ : IsUnit J.det) (h : Formalism.UG.cT σ g * J * g = J) : g.det * σ g.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (σ.map_det g).symm
  rw [h2] at h1
  apply hJ.mul_left_cancel
  linear_combination h1

theorem unitary_map {F E R S : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (h : Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J) :
    Formalism.UG.cT (sigR S σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom) * JR S J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = JR S J := by
  set π : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hπ
  have hs : ∀ z, π (sigR R σ z) = sigR S σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hπ, sigR]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hJ : (JR R J).map π = JR S J := by
    ext i j
    simp [hπ, JR, inclR]
  have hc : (Formalism.UG.cT (sigR R σ) g).map π = Formalism.UG.cT (sigR S σ) (g.map π) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hs]
  have h2 := congrArg (fun M => Matrix.map M π) h
  simp only [Matrix.map_mul] at h2
  rw [hJ, hc] at h2
  exact h2

theorem finHom_unitary {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (finHom V g).1 * JR (F := D.host.F) (Af D.host.F) V.gram * (finHom V g).1 =
      JR (F := D.host.F) (Af D.host.F) V.gram :=
  unitary_map (sndA D.host.F) D.sp.cm.sig V.gram (matHom V g).1
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finHom_herm_det : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ ((finHom V g).1 *ᵥ x) ((finHom V g).1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) ∧ (finHom V g).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V g).1.det = 1 ∧ ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det * sigR (AF D.host.F) D.sp.cm.sig ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det = 1 := by
  intro D V g
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R], IsUnit (JR (F := D.host.F) R V.gram).det := by
    intro R _ _
    have e : (JR (F := D.host.F) R V.gram).det = inclR (F := D.host.F) R V.gram.det := ((inclR (F := D.host.F) R).map_det V.gram).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne V)).map _
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · exact unit_form_inv _ _ _ (finHom_unitary V g) x y
  · exact unit_det_norm _ _ _ (hu _) (finHom_unitary V g)
  · exact unit_det_norm _ _ _ (hu _) (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointsGluePrincipalCover
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.Glue

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hh : Ideal.span (Set.range h) = ⊤) (f g : Sp (DualNumber S) ⟶ Y)
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ f =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ g) : f = g := by
  have := _root_.GlobalTheory.Frames.existsUnique_glue_dual S Y n h hh (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ g) (by
    intro i j α β hα hβ
    rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, dual_comp, dual_comp, hα, hβ])
  exact this.unique e fun _ => rfl

theorem exists_lift {S : Type} [CommRing S] {n : ℕ} {h : Fin n → S}
    (hh : Ideal.span (Set.range h) = ⊤) (p : Sp S) :
    ∃ (i : Fin n) (p' : Sp (Localization.Away (h i))), spMap (algebraMap S (Localization.Away (h i))) p' = p := by
  have hp : ∃ i, h i ∉ (show PrimeSpectrum S from p).asIdeal := by
    by_contra hc
    push Not at hc
    apply (show PrimeSpectrum S from p).isPrime.ne_top
    rw [eq_top_iff, ← hh, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hc i
  obtain ⟨i, hi⟩ := hp
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away (h i)) (h i)
  have : (show PrimeSpectrum S from p) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (h i)))) := by
    rw [hr]; exact hi
  obtain ⟨p', hp'⟩ := this
  exact ⟨i, p', hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
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

theorem secBC_unique {S T : Type} [CommRing S] [CommRing T] {φ : S →+* T} {a : S} {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} {s : LB.Sec (PPx x)} {t t' : LB.Sec (PPx x')} (h₁ : SecBC φ a x x' s t)
    (h₂ : SecBC φ a x x' s t') : t = t' := by
  obtain ⟨p₁, s₁, f₁, a₁⟩ := h₁
  obtain ⟨p₂, s₂, f₂, a₂⟩ := h₂
  have e : p₁ = p₂ := by
    apply pullback.hom_ext
    · exact f₁.trans f₂.symm
    · exact s₁.trans s₂.symm
  subst e
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht'⟩ := t'
  congr 1
  funext i
  exact (a₁ i (chart_le p₁ s₁ i)).symm.trans (a₂ i (chart_le p₁ s₁ i))

theorem secBC_transport {S S' T : Type} [CommRing S] [CommRing S'] [CommRing T] {φ : S →+* T} {ψ : S' →+* T}
    {x : Sp S ⟶ Xo.X} {x' : Sp S' ⟶ Xo.X} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} {w w' : Sp T ⟶ Xo.X}
    (hw : w = w') {r : LB.Sec (PPx w)} (h₁ : SecBC φ 1 x w s r) (h₂ : SecBC ψ 1 x' w s' r)
    (t : LB.Sec (PPx w')) (ht : SecBC φ 1 x w' s t) : SecBC ψ 1 x' w' s' t := by
  subst hw
  rw [secBC_unique ht h₁]
  exact h₂

def algOf {K S A B : Type} [CommRing K] [CommRing S] [CommRing A] [CommRing B] [Algebra K S] [Algebra S A]
    [Algebra S B] [Algebra K A] [Algebra K B] [IsScalarTower K S A] [IsScalarTower K S B] (α : A →+* B)
    (hα : α.comp (algebraMap S A) = algebraMap S B) : A →ₐ[K] B :=
  { α with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply K S A, IsScalarTower.algebraMap_apply K S B, ← hα]
      rfl }

end GlobalTheory.Frames.Glue


open GlobalTheory.Frames.Glue in
theorem GlobalTheory.Frames.frPt_glue : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∀ (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ y : ∀ i, FrPt Xo c (Localization.Away (h i)), (∀ i, (y i).x = spMap (algebraMap S (Localization.Away (h i))) ≫ x) → (∀ i j (α : Localization.Away (h i) →ₐ[c.F] Localization.Away (h i * h j)) (β : Localization.Away (h j) →ₐ[c.F] Localization.Away (h i * h j)), α.toRingHom.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.toRingHom.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ z, FrMap α (y i) z → FrMap β (y j) z) → ∃ y₀ : FrPt Xo c S, y₀.x = x ∧ ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y₀ (y i) := by
  intro hB E _ _ _ H Dw l Xo c S _ _ x hx n h hh y hy hov
  classical

  have ovl : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      ∃ z : FrPt Xo c (Localization.Away (h i * h j)),
        z.x = spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x ∧
        (∀ τ k, z.u τ k = spMap (dualMap α) ≫ (y i).u τ k) ∧ (∀ τ k, z.u τ k = spMap (dualMap β) ≫ (y j).u τ k) ∧
        SecBC α 1 _ _ (y i).s z.s ∧ SecBC β 1 _ _ (y j).s z.s := by
    intro i j α β hα hβ
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (algOf (K := c.F) α hα) (y i)
    have hz' := hov i j (algOf α hα) (algOf β hβ) hα hβ z hz
    have e₁ := ((_root_.GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ (y i)).2.2 z).1 hz
    have e₂ := ((_root_.GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ (y j)).2.2 z).1 hz'
    refine ⟨z, ?_, e₁.2.1, e₂.2.1, e₁.2.2, e₂.2.2⟩
    rw [e₁.1, hy i, ← Category.assoc, sp_comp, ← hα]
    rfl

  have nf : ∀ i, ∃ ov u tan eig basis s gen,
      y i = ⟨spMap (algebraMap S (Localization.Away (h i))) ≫ x, ov, u, tan, eig, basis, s, gen⟩ := by
    intro i
    have hi := hy i
    generalize y i = w at hi
    obtain ⟨wx, ov, u, tan, eig, basis, s, gen⟩ := w
    dsimp only at hi
    subst hi
    exact ⟨ov, u, tan, eig, basis, s, gen, rfl⟩
  choose ov u tan eig basis s gen hyy using nf
  obtain rfl : y = fun i => ⟨_, ov i, u i, tan i, eig i, basis i, s i, gen i⟩ := funext hyy
  dsimp only at ovl

  have hu : ∀ τ k, ∃ w₀ : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = u i τ k := by
    intro τ k
    refine (_root_.GlobalTheory.Frames.existsUnique_glue_dual S _ n h hh (fun i => u i τ k) ?_).exists
    intro i j α β hα hβ
    obtain ⟨z, -, h₁, h₂, -⟩ := ovl i j α β hα hβ
    exact (h₁ τ k).symm.trans (h₂ τ k)
  choose u₀ hu₀ using hu
  have eig₀ : ∀ τ k, IsEigAt c τ (u₀ τ k) := by
    intro τ k a
    refine dual_ext hh _ _ fun i => ?_
    rw [← Category.assoc, hu₀, eig i τ k a, ← hu₀ τ k i, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
      dual_eps, ← IsScalarTower.algebraMap_apply]
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  have tb : TanBasis x (fun j => u₀ (e j).1 (e j).2) := by
    refine GlobalTheory.TanBasisLocal.tanBasis_local E H Dw l Xo S x n h hh _ _ fun i => ?_
    have := (_root_.GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c _ _ (u i) _ e (tan i) (eig i)).1 (basis i)
    simpa only [hu₀] using this
  have tan₀ : ∀ τ k, IsTanAt x (u₀ τ k) := by
    intro τ k
    have := tb.1 (e.symm ⟨τ, k⟩)
    dsimp only at this
    rw [e.apply_symm_apply] at this
    exact this
  have basis₀ := (_root_.GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S x u₀ _ e tan₀ eig₀).2 tb

  obtain ⟨s₀, hs₀⟩ := (_root_.GlobalTheory.SecGlue.existsUnique_glue E H Dw l Xo S x n h hh s (by
    intro i j α β hα hβ t ht
    obtain ⟨z, hz, -, -, h₁, h₂⟩ := ovl i j α β hα hβ
    exact secBC_transport hz h₁ h₂ t ht)).exists
  have nz : SecNZ x s₀ := by
    intro p
    obtain ⟨i, p', rfl⟩ := exists_lift hh p
    exact (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S _ _ x _ rfl s₀ (s i) (hs₀ i) p').1
      (_root_.GlobalTheory.Frames.secNZ_of_secGen hB E H Dw l Xo _ _ (s i) (gen i) p')
  refine ⟨⟨x, hx, u₀, tan₀, eig₀, basis₀, s₀, _root_.GlobalTheory.Frames.secGen_of_secNZ hB E H Dw l Xo S x s₀ nz⟩, rfl, fun i => ?_⟩
  refine ((_root_.GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ _).2.2 _).2 ⟨rfl, fun τ k => (hu₀ τ k i).symm, hs₀ i⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProduct
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.LevelHalf

theorem map_comap_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) :
    (l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb := by
  refine le_antisymm Ideal.map_comap_le ?_
  have hw : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (LPb.w0K D) = H.w0 := by
    apply RingOfIntegers.ext
    have h2 : ((2 * H.w0 : 𝓞 D.host.E) : D.host.E) = ((1 + H.rt : 𝓞 D.host.E) : D.host.E) := by
      rw [H.two_weight_eq_one_add_root]
    have h3 : (2 : D.host.E) * (H.w0 : D.host.E) = 1 + (H.rt : D.host.E) := h2
    show ((1 + D.host.sqrtMinusD) / 2 : D.host.E) = (H.w0 : D.host.E)
    rw [← hrt, ← h3]
    field_simp
  conv_lhs => rw [l.fromK]
  rw [Ideal.span_le]
  rintro a ⟨ha, ha'⟩
  have hr : a ∈ (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)).toIntAlgHom.range := by
    refine Algebra.adjoin_le ?_ ha'
    rintro _ rfl
    exact ⟨LPb.w0K D, hw⟩
  obtain ⟨b, rfl⟩ := hr
  exact Ideal.mem_map_of_mem _ ha

theorem exists_prime_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {p : ℕ} (hp : p.Prime) (hpM : p ∣ l.M) :
    ∃ pb : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ pb.asIdeal ∧
      pb.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
  set I : Ideal (𝓞 D.host.K) := l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ⊔
    Ideal.span {(p : 𝓞 D.host.K)} with hI
  have hmap : I.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [hI, Ideal.map_sup, map_comap_half D H l hrt, Ideal.map_span, Set.image_singleton, map_natCast]
  have hbar : (Ideal.span {(p : 𝓞 D.host.E)}).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hnt := LPb.span_p_ne_top D hp
  have hle : Ideal.span {(p : 𝓞 D.host.K)} ≤ I := le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := congrArg Ideal.absNorm hJ
  rw [map_mul, LPb.absNorm_span_p] at hN
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN.symm)
  have hi1 : i = 1 := by
    interval_cases i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hieq
      rw [hieq, Ideal.map_top] at hmap
      have hmap' := congrArg (Ideal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) hmap
      rw [Ideal.map_top, Ideal.map_sup, hbar] at hmap'
      have hc := (Ideal.isCoprime_iff_sup_eq.2 hmap.symm).mul_left (Ideal.isCoprime_iff_sup_eq.2 hmap'.symm)
      rw [l.prod, Ideal.isCoprime_iff_sup_eq, sup_eq_right.2
        (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hpM))] at hc
      exact hnt hc
    · rfl
    · exfalso
      rw [hieq] at hN
      have hJ1 : Ideal.absNorm J = 1 :=
        Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN.symm.trans (mul_one _).symm)
      rw [Ideal.absNorm_eq_one_iff] at hJ1
      rw [hJ1, Ideal.mul_top] at hJ
      rw [← hJ, Ideal.map_span, Set.image_singleton, map_natCast] at hmap
      have h1 : l.Mb ≤ Ideal.span {(p : 𝓞 D.host.E)} := hmap ▸ le_sup_left
      have h2 : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {(p : 𝓞 D.host.E)} :=
        hbar ▸ Ideal.map_mono h1
      exact hnt (top_le_iff.1 (l.coprime ▸ sup_le h1 h2))
  rw [hi1, pow_one] at hieq
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hieq
    exact hp.ne_zero hieq.symm
  exact ⟨⟨I, hprime, hne⟩, hle (Ideal.subset_span rfl), hmap⟩

theorem eq_mul_sup {R : Type*} [CommRing R] (I : Ideal R) {a b : R} (hab : IsCoprime a b) (h : a * b ∈ I) :
    I = (I ⊔ Ideal.span {a}) * (I ⊔ Ideal.span {b}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, v, huv⟩ := hab
    have e : x = (u * a) * x + x * (v * b) := by linear_combination (-x) * huv
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
        (Ideal.mem_sup_left hx))
      (Ideal.mul_mem_mul (Ideal.mem_sup_left hx)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))))
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))

theorem good_and_half_eq_prod : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), (H.rt : D.host.E) = D.host.sqrtMinusD → l.M = D.host.g 0 * D.host.g 1 → (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  intro D H l hrt hM
  refine ⟨fun p _ => GlobalTheory.PinNum.goodAt_of_two_primes l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, ?_⟩
  have hd : ∀ k : Fin 2, D.host.g k ∣ l.M := by
    intro k
    rw [hM]
    fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  choose pb h1 h2 using fun k => exists_prime_half D H l hrt (D.host.g_prime k) (hd k)
  refine ⟨pb, h1, ?_⟩
  rw [Fin.prod_univ_two, h2 0, h2 1]
  apply eq_mul_sup
  · exact Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  · rw [← Nat.cast_mul, ← hM]
    have : Ideal.span {((l.M : ℕ) : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)

end GlobalTheory.LevelHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem infiniteAdele_bijective : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  intro D
  have hτ : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ (cF D x) = starRingEnd ℂ (τ x) :=
    fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : cF D ≠ 1 := by
    intro h
    have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
    have h1 := hτ D.host.φ₀ D.host.sqrtMinusD
    rw [h, AlgEquiv.one_apply] at h1
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    exact h0.2.2 (by linarith)
  have H := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E (cF D) D.sp.cm.deg2 hc D.sp.cm.totReal hτ
  refine ⟨?_, fun θ hθ => ?_⟩
  · choose θ hθ using H.1
    exact ⟨θ, hθ⟩
  · obtain ⟨h1, h2, h3⟩ := H.2 θ hθ
    refine ⟨h1, h2, h3 {τ | τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} fun τ => ?_⟩
    have := cm_type_mem_iff_conj_not_mem D τ
    rw [mem_cm_type_iff, mem_cm_type_iff] at this
    exact this

end GlobalTheory.Member
end
end

