module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem alg {G : Type*} [CommGroup G] (a P b G₁ G₃ : G) :
    a * P * b⁻¹ = G₁ * a * (G₁⁻¹ * P * G₃) * (G₃⁻¹ * b⁻¹) := by
  rw [mul_comm G₁ a]; group

theorem frame_cocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (hC : DescCompat f L φ) (hK : DescCocycle f L φ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ) (ht : ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) :
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by

  have hf : ∀ z : ↥(pullback f f), f (pullback.snd f f z) = f (pullback.fst f f z) := fun z => by
    change (pullback.snd f f ≫ f) z = (pullback.fst f f ≫ f) z
    rw [pullback.condition]
  set V' : (pullback f f).Opens := pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V with hV'
  let W : L.ι × L.ι → (pullback f f).Opens := fun p => chart f L p.1 p.2 ⊓ V'
  have le1 : ∀ p : L.ι × L.ι, W p ≤ pullback.fst f f ⁻¹ᵁ (f ⁻¹ᵁ V ⊓ L.U p.1) :=
    fun p z hz => ⟨hz.2, hz.1.1⟩
  have le2 : ∀ p : L.ι × L.ι, W p ≤ chart f L p.1 p.2 := fun p => inf_le_left
  have le3 : ∀ p : L.ι × L.ι, W p ≤ pullback.snd f f ⁻¹ᵁ (f ⁻¹ᵁ V ⊓ L.U p.2) :=
    fun p z hz => ⟨show f (pullback.snd f f z) ∈ V by rw [hf]; exact hz.2, hz.1.2⟩
  let u : ∀ p, Γ(pullback f f, W p)ˣ := fun p =>
    res (le1 p) (pullU (pullback.fst f f) _ (t p.1)) * res (le2 p) (φ p.1 p.2) *
      (res (le3 p) (pullU (pullback.snd f f) _ (t p.2)))⁻¹
  have key : ∀ {T : Scheme.{0}} (h : T ⟶ pullback f f) (y : T) (p : L.ι × L.ι) (hy : h y ∈ W p),
      gm h y (W p) (u p) = gm (h ≫ pullback.fst f f) y _ (t p.1) * gm h y _ (φ p.1 p.2) *
        (gm (h ≫ pullback.snd f f) y _ (t p.2))⁻¹ := by
    intro T h y p hy
    simp only [u, map_mul, map_inv]
    rw [gm_res h y (le1 p) hy, gm_res h y (le2 p) hy, gm_res h y (le3 p) hy,
      gm_pull h (pullback.fst f f) y _ (le1 p hy), gm_pull h (pullback.snd f f) y _ (le3 p hy)]

  have tpull : ∀ {T : Scheme.{0}} (h : T ⟶ X) (y : T) (i j : L.ι), f (h y) ∈ V → h y ∈ L.U i → h y ∈ L.U j →
      gm h y _ (t i) = gm h y _ (L.g i j) * gm h y _ (t j) := by
    intro T h y i j hV hi hj
    have hle1 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ V ⊓ L.U i := inf_le_inf_left _ inf_le_left
    have hle2 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_right
    have hle3 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ V ⊓ L.U j := inf_le_inf_left _ inf_le_right
    have e : res hle1 (t i) = res hle2 (L.g i j) * res hle3 (t j) := by
      apply unit_ext
      intro x hx
      rw [map_mul, gm_res _ x hle1 hx, gm_res _ x hle2 hx, gm_res _ x hle3 hx]
      exact ht i j x hx.1 hx.2.1 hx.2.2
    have hm : h y ∈ f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) := ⟨hV, hi, hj⟩
    have := congrArg (gm h y _) e
    rwa [map_mul, gm_res h y hle1 hm, gm_res h y hle2 hm, gm_res h y hle3 hm] at this
  have hW : ∀ p, W p ≤ V' := fun p => inf_le_right
  have hcov : V' ≤ iSup W := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩, hz⟩
  have hagree : ∀ p q, ∀ x ∈ W p ⊓ W q, gm (𝟙 _) x (W p) (u p) = gm (𝟙 _) x (W q) (u q) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ x ⟨hp, hq⟩
    rw [key (𝟙 _) x _ hp, key (𝟙 _) x _ hq]
    simp only [Category.id_comp]
    have hx1 : f (pullback.fst f f x) ∈ V := hp.2
    have hx2 : f (pullback.snd f f x) ∈ V := by rw [hf]; exact hx1
    rw [tpull (pullback.fst f f) x i' i hx1 hq.1.1 hp.1.1, tpull (pullback.snd f f) x j' j hx2 hq.1.2 hp.1.2,
      hC x i i' j j' hp.1.1 hq.1.1 hp.1.2 hq.1.2]
    have hg : gm (pullback.fst f f) x _ (L.g i' i) * gm (pullback.fst f f) x _ (L.g i i') = 1 := by
      rw [gm_cocycle hL _ x hq.1.1 hp.1.1 hq.1.1, gm_self hL _ x hq.1.1]
    rw [eq_inv_of_mul_eq_one_right hg, mul_inv]
    exact alg _ _ _ _ _
  obtain ⟨c, hc⟩ := glue_unit V' W hW hcov u hagree
  have cgerm : ∀ {T : Scheme.{0}} (h : T ⟶ pullback f f) (y : T) (p : L.ι × L.ι) (hy : h y ∈ W p),
      gm h y V' c = gm (h ≫ pullback.fst f f) y _ (t p.1) * gm h y _ (φ p.1 p.2) *
        (gm (h ≫ pullback.snd f f) y _ (t p.2))⁻¹ := by
    intro T h y p hy
    rw [← key h y p hy, ← hc p, gm_res h y (hW p) hy]
  refine ⟨c, ?_, ?_⟩
  · intro z i j hV hi hj
    have := cgerm (𝟙 _) z (i, j) ⟨⟨hi, hj⟩, hV⟩
    simpa only [Category.id_comp] using this
  · intro w hV
    set q₁ := pullback.fst (pullback.snd f f) (pullback.fst f f)
    set q₂ := pullback.snd (pullback.snd f f) (pullback.fst f f)
    have hmid : q₁ ≫ pullback.snd f f = q₂ ≫ pullback.fst f f := pullback.condition
    have h13a : pr13 f ≫ pullback.fst f f = q₁ ≫ pullback.fst f f := by unfold pr13; exact pullback.lift_fst _ _ _
    have h13b : pr13 f ≫ pullback.snd f f = q₂ ≫ pullback.snd f f := by unfold pr13; exact pullback.lift_snd _ _ _
    have pmid : pullback.snd f f (q₁ w) = pullback.fst f f (q₂ w) := by
      change (q₁ ≫ pullback.snd f f) w = (q₂ ≫ pullback.fst f f) w
      rw [hmid]
    have p13a : pullback.fst f f (pr13 f w) = pullback.fst f f (q₁ w) := by
      change (pr13 f ≫ pullback.fst f f) w = (q₁ ≫ pullback.fst f f) w
      rw [h13a]
    have p13b : pullback.snd f f (pr13 f w) = pullback.snd f f (q₂ w) := by
      change (pr13 f ≫ pullback.snd f f) w = (q₂ ≫ pullback.snd f f) w
      rw [h13b]
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (q₁ w))
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (q₁ w))
    obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (q₂ w))
    have hV2 : f (pullback.fst f f (q₂ w)) ∈ V := by rw [← pmid, hf]; exact hV
    have hV3 : f (pullback.fst f f (pr13 f w)) ∈ V := by rw [p13a]; exact hV
    have m1 : q₁ w ∈ W (i, j) := ⟨⟨hi, hj⟩, hV⟩
    have m2 : q₂ w ∈ W (j, k) := ⟨⟨show pullback.fst f f (q₂ w) ∈ L.U j by rw [← pmid]; exact hj, hk⟩, hV2⟩
    have m3 : pr13 f w ∈ W (i, k) := ⟨⟨show pullback.fst f f (pr13 f w) ∈ L.U i by rw [p13a]; exact hi,
      show pullback.snd f f (pr13 f w) ∈ L.U k by rw [p13b]; exact hk⟩, hV3⟩
    rw [cgerm q₁ w (i, j) m1, cgerm q₂ w (j, k) m2, cgerm (pr13 f) w (i, k) m3, hmid, h13a, h13b,
      ← hK w i j k hi hj hk]
    dsimp only
    simp only [q₁, q₂]
    group

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharP
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime]

theorem finrank_eq_of_semilinear_surjective {W k M V : Type} [CommRing W] [Nontrivial W] [Field k]
    [AddCommGroup M] [Module W M] [Module.Free W M] [Module.Finite W M] [AddCommGroup V] [Module k V]
    {σ : W →+* k} (hσ : Function.Surjective σ) {q : ℕ} (hq : (q : k) = 0) (r : M →ₛₗ[σ] V)
    (hr : Function.Surjective r) (hk : ∀ m, r m = 0 → ∃ n, m = q • n) :
    Module.Finite k V ∧ Module.finrank k V = Module.finrank W M := by
  let b := Module.finBasis W M
  have h1 : LinearIndependent k fun i => r (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    choose w hw using fun i => hσ (c i)
    obtain ⟨n, hn⟩ := hk (∑ i, w i • b i) (by simpa only [map_sum, map_smulₛₗ, hw] using hc)
    have e := congrArg (fun m => σ (b.repr m i)) hn
    simpa [hq, hw, Finsupp.single_apply] using e
  have h2 : ⊤ ≤ Submodule.span k (Set.range fun i => r (b i)) := fun v _ => by
    obtain ⟨m, rfl⟩ := hr v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr m, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨.of_basis (.mk h1 h2), by rw [Module.finrank_eq_card_basis (.mk h1 h2), Fintype.card_fin]⟩

section BaseChange

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S] {G H : PDivGroup p R}

end BaseChange

variable (hW : Published.BarsottiTateDieudonne.WittModule) {K : Type} [Field K] (h : (p : K) = 0)
include hW h


omit hW in
theorem range_rigExtMap_relFrob (G : PDivGroup p K) :
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span K (Set.range ⇑(SemiHom.rig (absFrob h G))) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    have induct (P : (frobTwist h G).RigExt → Prop)
        (htmul : ∀ (r : K) y, P (r • (frobProj h G).rig y))
        (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
      letI := (frobRing h).toAlgebra
      obtain ⟨y, rfl⟩ := (liftSemi_rig_bijective (R := K) K G h
        (.inl (@Module.Flat.of_free K K _ _ (_) (@Module.Free.of_divisionRing K K _ _ (_))))).2 x
      induction y using TensorProduct.inductionOn with
      | tmul r y => exact htmul r y
      | add x y hx hy => exact (congrArg P (map_add _ _ _)).mpr (hadd _ _ hx hy)
    refine induct (fun x => rigExtMap (relFrob h G) x ∈ _) (fun r y => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, rigExtMap_relFrob_rig]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [map_add (rigExtMap (relFrob h G))]
      exact add_mem hx hy
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rigExtMap_relFrob_rig h G y⟩


end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivarianceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  first | exact @GlobalTheory.DblScal.scalar_factors_through_det | exact GlobalTheory.DblScal.scalar_factors_through_det | (intros; apply GlobalTheory.DblScal.scalar_factors_through_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepFixesVacuumTensorSiegelParabolicInStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.InertDblPar.parD_fix | exact GlobalTheory.InertDblPar.parD_fix | (intros; apply GlobalTheory.InertDblPar.parD_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EpsRedFr

theorem epsRed_tangent_frX : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P hU y' hU' hy hev
  have h1 : ⊤ ≤ ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) ⁻¹ᵁ U.1 := by
    rw [Category.assoc]; exact GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hfst : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap c.F (DualNumber K)) = algebraMap c.F K :=
    RingHom.ext fun r => by simp
  refine GlobalTheory.FlagMod.xF_ext (Y := TF.Y) ?_ (GlobalTheory.FlagMod.frX_snd P) ?_
  · rw [Category.assoc, hy, GlobalTheory.DeRham.epsRed, spMap_comp', hfst]
  · have e : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 = ev (frX P ≫ TF.Y.j) U.1 hU := by
      have e0 : ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.1 h1 =
          (TrivSqZeroExt.fstHom K K K).toRingHom.comp (ev (y' ≫ TF.Y.j) U.1 hU') := by
        rw [← GlobalTheory.FlagMod.ev_spMap _ (y' ≫ TF.Y.j) U.1 hU' (by rw [← Category.assoc]; exact h1)]
        exact GlobalTheory.FlagMod.ev_congr (Category.assoc _ _ _) _ _ _
      rw [e0]
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, hev r]
      simp
    rw [← GlobalTheory.FlagMod.spMap_ev ((GlobalTheory.DeRham.epsRed K ≫ y') ≫ TF.Y.j) U.2 h1,
      ← GlobalTheory.FlagMod.spMap_ev (frX P ≫ TF.Y.j) U.2 hU, e]

end GlobalTheory.EpsRedFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentBasisPulledFrameCompatiblePointChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.Vec

open TopologicalSpace GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO LieG)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [CommRing k] {x : Sp k ⟶ S}
  {G₁ : Over (Sp k)} [GrpObj G₁] {φ : G₁.left ⟶ G.left}

def form (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) :
    (Scheme.Modules.pullback x).obj (omega G) ⟶ GlobalTheory.structureModule (Sp k) :=
  omegaBase h ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso k).hom

theorem form_app (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {T : (Sp k).Opens}
    (s : Γ((Scheme.Modules.pullback x).obj (omega G), T)) :
    (form h p).app T s = dualApp (tangent p) le_top ((omegaBase h).app T s) := rfl

theorem pre_le (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W :=
  preimage_le_of_lieG p (le_of_sq (unitSec_comp h) hW hT)

theorem form_dUnit (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(G.left, W))
    (a b : Γ(Sp k, T))
    (e : ((p.1.left ≫ φ).appLE W _ (pre_le h p hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (form h p).app T (pullbackSections x (omega G) hT (dUnit G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  rw [form_app, omegaBase_dUnit h hW hT (le_of_sq (unitSec_comp h) hW hT) le_rfl]
  exact dualApp_tangent_dUnit p _ _ hV le_rfl (pre_le h p hW hT) a b
    ((appLE_appLE rfl _ _ _ f).trans e)

variable {k' : Type} [CommRing k'] (r : k →+* k') (F : DualNumber k →+* DualNumber k')

theorem spMap_comp_hom (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a)) :
    spMap F ≫ (specO k (DualNumber k)).hom = (specO k' (DualNumber k')).hom ≫ spMap r := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext hF)

theorem spMap_epsFn (he : F DualNumber.eps = DualNumber.eps) :
    (spMap F).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F)) DualNumber.eps).symm.trans ?_
  exact congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom he

theorem epsZero_spMap (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) :
    sec (epsZero k') ≫ spMap F = spMap r ≫ sec (epsZero k) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (F a).fst = r a.fst
  have : a = algebraMap k _ a.fst + algebraMap k _ a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [this, map_add (f := _), map_mul, hF, hF, he]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {G₂ : Over (Sp k')} [GrpObj G₂] {ψ : G₂.left ⟶ G.left}

theorem form_baseChange [QuasiSeparated G.hom] (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) (q : LieG G₂) (hq : q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ)
    {V : S.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (spMap r ≫ x) ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      (spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤)) := by
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := GlobalTheory.Conormal.exists_isChart (sec_hom (MonObj.one (X := G))) (V := V)
      (x := x (spMap r y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap r y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := G))) (resM _ hle s)
    have hf' : dUnit G c.le f = resM (omega G) hle s := hf
    have hTU' : spMap r ⁻¹ᵁ T ≤ (spMap r ≫ x) ⁻¹ᵁ U := (spMap r).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      ((p.1.left ≫ φ).appLE W _ (pre_le h₁ p c.le hTU) f)
    have e₁ := form_dUnit h₁ p c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        spMap F ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_comp_hom r F hF)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap r) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap F).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap r).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_comp_hom r F hF) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap F).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_epsFn F he)))
    have e₂ := form_dUnit h₂ q c.le hTU' f ((spMap r).appLE T _ le_rfl a)
      ((spMap r).appLE T _ le_rfl b) (by
        refine (appLE_appLE hq.symm (pre_le h₁ p c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap F).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap r ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (form h₂ q) le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap r) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap r) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (form h₁ p) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem exists_lieG (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) : ∃ q : LieG G₂, q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := by
  have w : (spMap F ≫ p.1.left ≫ φ) ≫ G.hom = (specO k' (DualNumber k')).hom ≫ spMap r ≫ x := by
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc p.1.left, Over.w p.1, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ x) (spMap_comp_hom r F hF)
  let q : specO k' (DualNumber k') ⟶ G₂ :=
    Over.homMk (h₂.1.lift _ (specO k' (DualNumber k')).hom w) (h₂.1.lift_snd _ _ _)
  have hq : q.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := h₂.1.lift_fst _ _ _
  have ht : (toUnit (specO k' k')).left = 𝟙 (Sp k') := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  refine ⟨⟨q, Over.OverMorphism.ext (h₂.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hq⟩
  rw [Over.comp_left, Over.comp_left, ht, Category.assoc, hq, Category.assoc]
  have e : sec (epsZero k') ≫ spMap F ≫ p.1.left ≫ φ = (spMap r ≫ x) ≫ unitSec G := by
    rw [← Category.assoc, epsZero_spMap r F hF he, Category.assoc, ← Category.assoc (sec _), sec_epsZero_comp,
      unitSec_comp h₁, Category.assoc]
  exact e.trans ((unitSec_comp h₂).symm.trans (Category.id_comp _).symm)

theorem dual_vec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  rintro S G _ _ g c R R' _ _ ξ r _ y y' rfl hG - ⟨hc, hy⟩ ⟨hc', hy'⟩ F hF he j
  obtain ⟨p, hp, hp'⟩ := hy j
  obtain ⟨q, hq, hq'⟩ := hy' j
  have h₁ := isGrpPullback_pullback G ξ
  have h₂ := isGrpPullback_pullback G (spMap r ≫ ξ)
  obtain ⟨w, hw⟩ := exists_lieG r F hF he h₁ h₂ p
  have hfr : VB.IsFrame (pfr c (spMap r ≫ ξ) hc') := by
    have k₁ := ((c.isFrame.pullback (spMap r ≫ ξ)).res hc').map_iso (omegaBase h₂)
    have k₂ (b : Fin g) : resM _ hc' (pullbackSections (spMap r ≫ ξ) (omega G) le_rfl (c.e b)) =
        pullbackSections (spMap r ≫ ξ) (omega G) hc' (c.e b) := QCoh.res_pullbackSections _ _ _ _ _
    simp only [k₂] at k₁
    exact k₁
  obtain rfl : w = q := tangent_injective R' _ (hfr.dual_ext le_rfl fun b => by
    rw [resM_self]
    refine (form_baseChange r F hF he h₁ h₂ p w hw hc hc' (c.e b)).trans ?_
    refine .trans (congrArg ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)) (hp' b)) (.trans ?_ (hq' b).symm)
    exact (apply_ite _ _ _ _).trans (if_congr Iff.rfl
      (map_one ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom) (map_zero ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom)))
  rw [← hq, ← hp]
  exact hw

end GlobalTheory.KeyVals.Vec

end
end

