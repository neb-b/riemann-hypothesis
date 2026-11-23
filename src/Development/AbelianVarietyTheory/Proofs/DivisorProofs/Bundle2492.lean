module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEighthPowerElementaryMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_of_coords {S : Scheme.{0}} {B C X : Over S} [GrpObj B] [GrpObj C] [GrpObj X]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a)
    (z : X ⟶ B) (h : ∀ a, IsMonHom (z ≫ pr a)) : IsMonHom z := by
  have hm : ∀ (T : Over S) (x y : T ⟶ X), (x * y) ≫ z = (x ≫ z) * (y ≫ z) := by
    intro T x y
    refine (huniv T (fun a => (x * y) ≫ z ≫ pr a)).unique (fun a => Category.assoc _ _ _) (fun a => ?_)
    haveI := hpr a
    haveI := h a
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← MonObj.mul_comp]
  exact { one_hom := by
            rw [MonObj.one_eq_one, MonObj.one_eq_one]
            exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ X ↦ x ≫ z) (hm _))
          mul_hom := by
            rw [MonObj.mul_eq_mul, hm, MonObj.mul_eq_mul, MonObj.comp_mul]
            simp }

theorem isMonHom_one {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] : IsMonHom (1 : B ⟶ C) :=
  inferInstanceAs (IsMonHom (toUnit B ≫ η[C]))

theorem exists_incl {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a) :
    ∃ z : Fin 8 → (C ⟶ B), (∀ u, IsMonHom (z u)) ∧ ∀ u v, z u ≫ pr v = if v = u then 𝟙 C else 1 := by
  choose z hz _ using fun u : Fin 8 => huniv C (fun v => if v = u then 𝟙 C else 1)
  refine ⟨z, fun u => isMonHom_of_coords pr hpr huniv (z u) fun a => ?_, hz⟩
  rw [hz u a]
  split_ifs
  · infer_instance
  · exact isMonHom_one

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_prod {S : Scheme.{0}} {X M : Over S} [GrpObj X] [GrpObj M] [IsCommMonObj M] {J : Type}
    (f : J → (X ⟶ M)) (hf : ∀ i, IsMonHom (f i)) (s : Finset J) : IsMonHom (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty]; exact isMonHom_one
  · intro a s ha ih
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact inferInstanceAs (IsMonHom (lift (f a) (∏ i ∈ s, f i) ≫ μ[M]))

theorem prod_comp {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] [IsCommMonObj M] [IsCommMonObj N] {J : Type}
    (f : J → (X ⟶ M)) (s : Finset J) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, f i ≫ g := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8


open PowChar in
theorem characters_eighthPower_elementaryMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W _ pr hpr huniv _ pG hpG hgen c hc
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have ext : ∀ {H H' : Over (Sp R)} [GrpObj H] [GrpObj H'], IsSemiAbelian H → IsSemiAbelian H' →
      ∀ (F₁ F₂ : H ⟶ H'), IsMonHom F₁ → IsMonHom F₂ →
        (Over.pullback (jK R)).map F₁ = (Over.pullback (jK R)).map F₂ → F₁ = F₂ := by
    intro H H' _ _ h h' F₁ F₂ h₁ h₂ e
    exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) H H' h h' _ inferInstance).unique
      ⟨h₁, e⟩ ⟨h₂, rfl⟩
  obtain ⟨z, hzm, hz⟩ := exists_incl pr hpr huniv
  have hic : ∀ u, ∃ ic : G ⟶ G', IsMonHom ic ∧ (Over.pullback (jK R)).map ic = U.gen.hom ≫ z u ≫ U'.gen.inv := by
    intro u
    haveI := hzm u
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G G' hG hG'
      (U.gen.hom ≫ z u ≫ U'.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose ic hicm hicg using hic
  have hicp : ∀ u v, ic u ≫ pG v = if v = u then 𝟙 G else 1 := by
    intro u v
    haveI := hicm u
    haveI := hpG v
    have key : (Over.pullback (jK R)).map (ic u ≫ pG v) ≫ U.gen.hom = U.gen.hom ≫ (if v = u then 𝟙 A.A else 1) := by
      rw [Functor.map_comp, Category.assoc, hgen v, ← Category.assoc, hicg u]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hz u v]
    by_cases h : v = u
    · rw [if_pos h] at key ⊢
      refine ext hG hG _ _ inferInstance inferInstance ?_
      rw [← cancel_mono U.gen.hom, key, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [if_neg h] at key ⊢
      refine ext hG hG _ _ inferInstance isMonHom_one ?_
      rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  have hpw : ∀ w, (∏ v, pG v ≫ ic v) ≫ pG w = pG w := by
    intro w
    haveI := hpG w
    rw [PowChar.prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hicp w w, if_pos rfl, Category.comp_id]
    · intro v _ hv
      rw [Category.assoc, hicp v w, if_neg (Ne.symm hv), MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hprod : (∏ v, pG v ≫ ic v) = 𝟙 G' := by
    have hm : IsMonHom (∏ v, pG v ≫ ic v) :=
      isMonHom_prod _ (fun v => by haveI := hpG v; haveI := hicm v; infer_instance) _
    refine ext hG' hG' _ _ hm inferInstance ?_
    rw [CategoryTheory.Functor.map_id, ← cancel_mono U'.gen.hom, Category.id_comp]
    refine (huniv _ (fun w => U'.gen.hom ≫ pr w)).unique (fun w => ?_) (fun w => rfl)
    rw [Category.assoc, ← hgen w, ← Category.assoc, ← Functor.map_comp, hpw w]
  have hinj : Function.Injective (RingHom.id R) := Function.injective_id
  have hk : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ h => h
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch R hR G' hG' D' A' U' G hG D A U (ic u) (hicm u)
  obtain ⟨hid, hone, -⟩ := torMatch_id_one_mul R hR G hG D A U G hG D A U
  obtain ⟨hid', hone', hmul'⟩ := torMatch_id_one_mul R hR G' hG' D' A' U' G' hG' D' A' U'
  obtain ⟨-, hone'', -⟩ := torMatch_id_one_mul R hR G hG D A U G' hG' D' A' U'
  have hdc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG v).left R hR G hG D A U
      (RingHom.id R) (ic u).left hinj hk (c v) (d u) (hc v) (hd u)
    rw [← Over.comp_left, hicp u v, RingHom.id_comp] at h1
    by_cases h : v = u
    · rw [if_pos h] at h1 ⊢
      rw [Over.id_left] at h1
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hid
    · rw [if_neg h] at h1 ⊢
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hone
  have hcd : ∑ v, (c v).comp (d v) = AddMonoidHom.id _ := by
    have hs : ∀ s : Finset (Fin 8), TorMatch U' U' (RingHom.id R) (∏ v ∈ s, pG v ≫ ic v).left
        (∑ v ∈ s, (c v).comp (d v)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · rw [Finset.prod_empty, Finset.sum_empty]
        exact hone'
      · intro a s ha ih
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have h1 := torMatch_comp R hR G' hG' D' A' U' R hR G hG D A U (RingHom.id R) (ic a).left R hR G' hG' D' A' U'
          (RingHom.id R) (pG a).left hinj hk (d a) (c a) (hd a) (hc a)
        rw [← Over.comp_left, RingHom.id_comp] at h1
        exact hmul' _ _ _ _ h1 ih
    have h2 := hs Finset.univ
    rw [hprod, Over.id_left] at h2
    exact torMatch_unique R hR G' hG' D' A' U' R hR G' hG' D' A' U' _ _ hinj _ _ h2 hid'
  refine ⟨?_, ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x u => d u x, fun y => ?_, fun x => ?_⟩
    · funext u
      have e : ∀ v, d u (c v (y v)) = if v = u then y v else 0 := fun v => by
        have := DFunLike.congr_fun (hdc u v) (y v)
        rw [AddMonoidHom.comp_apply] at this
        rw [this]
        split_ifs <;> rfl
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have := DFunLike.congr_fun hcd x
      simpa using this
  · intro a b f f₁ m hf hf₁ hff₁ hm w x
    haveI := hf
    haveI := hpG w
    have hfp : f ≫ pG w = if w = a then pG b else 1 := by
      have key : (Over.pullback (jK R)).map (f ≫ pG w) ≫ U.gen.hom = U'.gen.hom ≫ (if w = a then pr b else 1) := by
        rw [Functor.map_comp, Category.assoc, hgen w, ← Category.assoc, hff₁, Category.assoc, hf₁.2 w]
      by_cases h : w = a
      · rw [if_pos h] at key ⊢
        refine ext hG' hG _ _ inferInstance (hpG b) ?_
        rw [← cancel_mono U.gen.hom, key, hgen b]
      · rw [if_neg h] at key ⊢
        refine ext hG' hG _ _ inferInstance isMonHom_one ?_
        rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG w).left R hR G' hG' D' A' U'
      (RingHom.id R) f.left hinj hk (c w) m (hc w) (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G' hG' D' A' U' f hf m hm)
    rw [← Over.comp_left, hfp, RingHom.id_comp] at h1
    have e : m.comp (c w) = if w = a then c b else 0 := by
      by_cases h : w = a
      · rw [if_pos h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 (hc b)
      · rw [if_neg h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 hone''
    have := DFunLike.congr_fun e x
    rw [AddMonoidHom.comp_apply] at this
    rw [this]
    split_ifs <;> rfl

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOnOfTExpGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumMult

theorem chartExpOn_of_tExp_gen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (e : ℕ) (b : thickObj R I e G ⟶ thickObj R I e G) (n : ℕ)
    (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U b n 0) (hF : Small I (w := id) F)
    (hf : ∀ β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f β) x z J = sval (F β) x z J)
    (hτ : TExp U τ (w := id) F) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W))
    (hg : ∀ (z : (thickObj R I e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG I e G).left) = i' 0 →
      gs (𝟙 _) z W g = sval τ (𝟙 _) z J') : ChartExpOn U e n i' W g f := by
  classical
  let S : Finset D.toPre.X := (hF e).toFinset
  have hS : ∀ α ∉ S, Van I (F α) e := fun α hα => by_contra fun h => hα ((hF e).mem_toFinset.2 h)
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    have h0 : sval (f α) (DVR.pGl U e) y J = 0 := (hf α _ _ y J hJ).trans (hS α hα _ (U.gt e).q.left y J hJ)
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ h0).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ jf jt hj hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy.1) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy.1) a.2])
    obtain ⟨J', hJ', eJ'⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit.{1}) (fun _ => 𝟙 _ ≫ (fstG I e G).left)
      (fun _ => p₂ PUnit.unit) (fun _ _ _ => rfl) (fun _ => mem_pull.1 hy.1.1.1.2)
    have e₀ : J (𝟙 _ ≫ (U.gt e).pG.left) = p₁ PUnit.unit := by rw [Category.id_comp]; exact eJ (.inl PUnit.unit)
    have e₁ : J' (𝟙 _ ≫ (fstG I e G).left) = p₂ PUnit.unit := eJ' PUnit.unit
    have H := hτ S hS _ (𝟙 _) y J J' hJ hJ'
    rw [evalE, zpow_zero, _root_.mul_one, zpow_natCast, e₀, e₁] at H
    refine ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y inf_le_right hy g).trans
      (hg y J' hy.2 hJ' (e₁.trans hj.symm))))).trans
      (H.trans (Eq.symm ?_))
    · rw [← Units.val_pow_eq_pow_val, gs_unit (𝟙 _) y _ hy, map_pow]
      exact congrArg (fun u => (u ^ n).val) (gm_res (𝟙 _) y _ hy _)
    · refine (DVR.gs_fsum (𝟙 _) y _ hy _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
      have l₁ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expW_le_f e (p₁, p₂) i' jf jt α.2)
      have l₂ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expWeight_le_chart_weight e (p₁, p₂) i' jf jt α.2)
      have a₁ := (gs_res (𝟙 _) y l₁ hy (((DVR.pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
        (gs_pull (𝟙 _) (DVR.pGl U e) y (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hy) ((f α.1).f (jf α.1)))
      have a₂ := (gs_unit (𝟙 _) y _ hy (res l₂ ((DVR.tG U e α.1).s (jt α.1)))).trans
        (congrArg Units.val (gm_res (𝟙 _) y l₂ hy _))
      have b₁ := sval_of (f α.1) (𝟙 _ ≫ DVR.pGl U e) y J (jf α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inl (α, a))))
      have b₂ := val_of (DVR.tG U e α.1) (𝟙 _) y J (jt α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (α, a))))
      exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (a₁.trans (b₁.symm.trans (hf α.1 _ _ y J hJ)))
        (a₂.trans (congrArg Units.val b₂.symm)))

theorem chartExpOn_of_tExp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U.toUnifPre b n 0), Small (maximalIdeal R) (w := id) F → (∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f β) x z J = sval (F β) x z J)) → TExp U.toUnifPre τ (w := id) F → ∀ (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R (maximalIdeal R) e G).left.Opens) (g : Γ((thickObj R (maximalIdeal R) e G).left, W)), (∀ (z : (thickObj R (maximalIdeal R) e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG (maximalIdeal R) e G).left) = i' 0 → gs (𝟙 _) z W g = sval τ (𝟙 _) z J') → GlobalTheory.MumMult.ChartExpOn U.toUnifPre e n i' W g f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U e b n F f τ hF hf hτ i' W g hg =>
    chartExpOn_of_tExp_gen U.toUnifPre e b n F f τ hF hf hτ i' W g hg

end GlobalTheory.MumMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_valuationSubring_of_image : ∀ (F : Type) [Field F] (V : ValuationSubring F) (T : Type) [CommRing T] [IsLocalRing T] (g : V →+* T), IsLocalHom g → ∀ (W' : Type) [CommRing W'] [IsDomain W'] [IsLocalRing W'] (io : T →+* W'), Function.Injective io → io.Finite → ∀ (Ω : Type) [Field Ω] (iF : F →+* Ω) (e : W' →+* Ω), Function.Injective e → (∀ v : V, iF v = e (io (g v))) → ∀ (y : F) (w : W'), iF y = e w → y ∈ V := by
  intro F _ V T _ _ g hg W' _ _ _ io hioi hiof Ω _ iF e he hi y w hy
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hiof.to_isIntegral hioi
  by_contra hyV
  have hy0 : y ≠ 0 := fun h => hyV (h ▸ V.zero_mem)
  have hinv : y⁻¹ ∈ V := (V.mem_or_inv_mem y).resolve_left hyV
  let u : V := ⟨y⁻¹, hinv⟩
  have hu : ¬ IsUnit u := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h' : y⁻¹ * (v : F) = 1 := by simpa [u] using congrArg Subtype.val hv
    have hv' : (v : F) = y := by
      calc (v : F) = y * (y⁻¹ * v) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hy0, _root_.one_mul]
        _ = y := by rw [h', _root_.mul_one]
    exact hyV (hv' ▸ v.2)
  have hprod : io (g u) * w = 1 := by
    apply he
    rw [map_mul, map_one, ← hi u, ← hy, ← map_mul]
    simp [u, inv_mul_cancel₀ hy0]
  exact hu ((isUnit_map_iff g u).1 ((isUnit_map_iff io (g u)).1 (IsUnit.of_mul_eq_one _ hprod)))

theorem chartVal_mem_of_dominates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hx hcl F _ β V hV h1 h2
  obtain ⟨T, _, _, _, lam, g, φ, hT, hgi', hgl, hgl', hφi, hφl, hξ⟩ :=
    _root_.GlobalTheory.Mum.trait_at_closed_point R M G Y α t hpb.w W hWa x hx hcl F β V hV h1 h2
  obtain ⟨W', _, _, _, io, σ, hW', hioi, hiof, hag⟩ := hs T hT φ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) hφi hφl hξ
  let e : W' →+* FractionRing W' := algebraMap W' (FractionRing W')
  have he : Function.Injective e := IsFractionRing.injective W' (FractionRing W')
  have hgg : Function.Injective ((e.comp io).comp g) := he.comp (hioi.comp hgi')
  let iF : F →+* FractionRing W' := IsFractionRing.lift hgg
  have hi : ∀ v : V, iF v = e (io (g v)) := fun v => IsFractionRing.lift_algebraMap hgg v
  have hαW := GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hWa
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.Mum.chartVal_mem_range_of_agree G.left M.S Y G.hom L hL α k s j W hW hWa hαW T lam W' io σ hag (FractionRing W') (iF.comp β) e
    (fun c => (hi ⟨_, h1 c⟩).trans (by rw [hgl' c]))
  have hw' : iF (β (chartVal L α s j W hW)) = e w := hw
  exact mem_valuationSubring_of_image F V T g hgl W' io hioi hiof (FractionRing W') iF e he hi (β (chartVal L α s j W hW)) w hw'

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureLowerTriangularPositiveDiagonal
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem conn_lowerTriangular {n s : ℕ} {T : V n → Matrix (Fin s) (Fin s) ℂ} {x : V n}
    (h0 : ∀ᶠ y in 𝓝 x, ∀ i j, i < j → T y i j = 0) (hd : ∀ i, T x i i ≠ 0) (ξ : V n) :
    (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
  have hT : (T x)ᵀ.BlockTriangular id := fun i j hij => h0.self_of_nhds j i hij
  have hu' : IsUnit (T x)ᵀ.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have hu : IsUnit (T x).det := by rwa [Matrix.det_transpose] at hu'
  have hD : (mdel T x ξ)ᵀ.BlockTriangular id := fun i j hij => by
    rw [Matrix.transpose_apply, mdel_apply,
      del_congr (g := fun _ => (0 : ℂ)) (h0.mono fun y hy => hy j i hij)]
    simp
  letI := Matrix.invertibleOfIsUnitDet _ hu'
  have hc : (conn T x ξ).BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular hT).mul hD
  refine ⟨fun i j hij => hc hij, fun i => ?_⟩
  have h := congrFun (congrFun (transpose_mul_conn hu ξ) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.transpose_apply, Matrix.transpose_apply,
    mdel_apply] at h
  · rw [← h, inv_mul_cancel_left₀ (hd i)]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hT (show id k < id i from hk), zero_mul]
    · rw [hc (show id i < id k from hk), mul_zero]
  · simp

theorem curv_lowerTriangular : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  intro n s T d v hT hd he ξ η
  have h0 : ∀ᶠ y in 𝓝 v, ∀ i j, i < j → T y i j = 0 := he.mono fun _ h => h.1
  have hv : ∀ i, T v i i ≠ 0 := fun i => by
    rw [he.self_of_nhds.2 i]; exact_mod_cast (hd i).ne'
  have hne : ∀ᶠ y in 𝓝 v, ∀ i, T y i i ≠ 0 :=
    eventually_all.2 fun i => (hT i i).continuousAt.eventually_ne (hv i)
  have hc : ∀ᶠ x in 𝓝 v, (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
    filter_upwards [h0.eventually_nhds, hne] with x h1 h2
    exact conn_lowerTriangular h1 h2 ξ
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [curv, Matrix.neg_apply, mdbar_apply,
      dbar_congr (g := fun _ => (0 : ℂ)) (hc.mono fun y hy => hy.1 i j hij)]
    simp
  · let H : V n → Matrix (Fin 1) (Fin 1) ℂ := fun x => Matrix.of fun _ _ => T x i i
    have hH : ∀ᶠ x in 𝓝 v, conn T x ξ i i = conn H x ξ 0 0 := by
      filter_upwards [hc, hne] with x h1 h2
      rw [h1.2 i, (conn_lowerTriangular (T := H)
        (Eventually.of_forall fun _ a b hab => absurd (Subsingleton.elim a b) hab.ne)
        (fun _ => h2 i) ξ).2 0]
      rfl
    have hs : ContDiffAt ℝ 2 (d i) v := by
      have h1 : ContDiffAt ℝ 2 (fun x => (T x i i).re) v :=
        Complex.reCLM.contDiff.contDiffAt.comp v ((hT i i).of_le (by norm_cast))
      refine h1.congr_of_eventuallyEq (he.mono fun x hx => ?_)
      simp [hx.2 i]
    rw [← curv_line (H := H) hs (hd i).ne' (he.mono fun x hx => hx.2 i) ξ η 0 0, curv, curv,
      Matrix.neg_apply, Matrix.neg_apply, mdbar_apply, mdbar_apply, dbar_congr hH]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormNewtonIdentitiesCurvaturePowerSums
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem newton_charpolyRev {R r : Type} [CommRing R] [Fintype r] [DecidableEq r] (M : Matrix r r R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | k
  · simp
  · have h := congrArg (PowerSeries.coeff k) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg, mul_comm (M.charpolyRev : PowerSeries R),
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    rw [mul_comm]
    simpa using h

theorem chernAt_newton (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) :
    chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j =
      -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  refine ⟨?_, fun j => ?_⟩
  · have h : (Matrix.charpolyRev (-curvPoly G v)).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    rw [chernAt, chernPoly, h, map_one, pow_zero, one_smul]
  · have h := congrArg (MvPolynomial.aeval (R := ℂ) (sym (n := n))) (newton_charpolyRev (-curvPoly G v) j)
    have hp (k : ℕ) : MvPolynomial.aeval (R := ℂ) (sym (n := n)) ((-curvPoly G v) ^ k).trace =
        (-1 : ℂ) ^ k • powAt G v k := by
      have e : curvEv G v ^ k = (curvPoly G v ^ k).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))) :=
        (map_pow (MvPolynomial.aeval (R := ℂ) (sym (n := n))).mapMatrix (curvPoly G v) k).symm
      rw [← neg_one_smul ℂ (curvPoly G v), smul_pow, Matrix.trace_smul, map_smul, powAt, e]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_natCast, map_neg, map_sum] at h
    simp only [map_mul, hp] at h
    simp only [chernAt, chernPoly]
    rw [smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, h, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - (i + 1), by omega⟩
    rw [show i + 1 + m - 1 - i = m by omega, neg_pow kappa]
    ring

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChern
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem chernTop_eq_mixTop {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n) :
    chernTop (MvPolynomial.X ((), n)) G v =
      (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  rw [chernTop, MvPolynomial.aeval_X, _root_.GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop]

end GlobalTheory.GoodTop
end

