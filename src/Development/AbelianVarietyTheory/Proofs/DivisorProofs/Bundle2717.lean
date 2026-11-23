module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartOneOfSemistableReductionPadicPolarized
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetCosetRepsBoundedHalfPoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {a b : ℕ}

theorem frAt_sub_reps (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D))
    (x y : Mx D b a) : frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Comparison₂.fr_sub, Matrix.map_sub _ (map_sub (cpt (D := D) w))]

theorem isOpen_valBall_reps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

theorem exists_finset_cosetReps : ∀ {D : D7} {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D))
    (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ), IsIdemSum e P → ∃ R : Finset (Mx D b a),
    (∀ r ∈ R, IsHalf e r ∧ IsSmall P β' β (-(n : ℤ)) r) ∧
    (∀ t, IsHalf e t → IsSmall P β' β (-(n : ℤ)) t → ∃ r ∈ R, IsSmall P β' β n (t - r)) ∧
    ∀ r ∈ R, ∀ r' ∈ R, IsSmall P β' β n (r - r') → r = r' := by
  intro D a b β' β P e n _
  classical
  let V := (w : P) → Fin b → Fin a → Kw w.1
  let φ : Mx D b a → V := fun t w r s => frAt w.1 β' β t r s
  have hφ : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y; funext w r s
    show frAt _ β' β (x - y) r s = frAt _ β' β x r s - frAt _ β' β y r s
    rw [frAt_sub_reps]; rfl
  let ρ : ∀ w : P, ValueGroupWithZero (Kw w.1) := fun w =>
    valuation (Kw w.1) ((unifAt w.1 ^ (n : ℤ) : (Kw w.1)ˣ) : Kw w.1)
  have hρ : ∀ w, ρ w ≠ 0 := fun w => by simp [ρ]
  let H : AddSubgroup V :=
    { carrier := {x | ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w}
      add_mem' := fun {x y} hx hy w r s =>
        ((valuation (Kw w.1)).map_add _ _).trans (max_le (hx w r s) (hy w r s))
      zero_mem' := fun w r s => by
        show valuation _ (0 : Kw w.1) ≤ _
        rw [map_zero]; exact zero_le'
      neg_mem' := fun {x} hx w r s => by
        show valuation _ (-(x w r s)) ≤ _
        rw [Valuation.map_neg]; exact hx w r s }
  have hH : ∀ x : V, x ∈ H ↔ ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w := fun x => Iff.rfl
  have hHset : (H : Set V) = Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s =>
      {z : Kw w.1 | valuation (Kw w.1) z ≤ ρ w} := by
    ext x
    rw [SetLike.mem_coe, hH]
    constructor
    · intro h
      exact Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s
    · intro h w r s
      exact Set.mem_univ_pi.1 (Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h w) r) s
  have hHo : IsOpen (H : Set V) := by
    rw [hHset]
    exact isOpen_set_pi Set.finite_univ fun w _ => isOpen_set_pi Set.finite_univ fun r _ =>
      isOpen_set_pi Set.finite_univ fun s _ => isOpen_valBall_reps _ (hρ w)
  let K : Set V := Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s =>
      {z : Kw w.1 | valuation (Kw w.1) z ≤
        valuation (Kw w.1) ((unifAt w.1 ^ (-(n : ℤ)) : (Kw w.1)ˣ) : Kw w.1)}
  have hK : IsCompact K := isCompact_univ_pi fun w => isCompact_univ_pi fun r => isCompact_univ_pi fun s =>
    IsNonarchimedeanLocalField.isCompact_closedBall _ _
  let U : V → Set V := fun x => (fun y => y - x) ⁻¹' (H : Set V)
  have hUo : ∀ x, IsOpen (U x) := fun x => hHo.preimage (continuous_id.sub continuous_const)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, by
    simp [U, H.zero_mem]⟩)
  have hsmall : ∀ (m : ℤ) t, IsSmall P β' β m t ↔ ∀ (w : P) r s,
      valuation (Kw w.1) (φ t w r s) ≤ valuation (Kw w.1) ((unifAt w.1 ^ m : (Kw w.1)ˣ) : Kw w.1) := by
    intro m t
    exact ⟨fun h w r s => h w.1 w.2 r s, fun h w hw r s => h ⟨w, hw⟩ r s⟩
  let S : Set (Mx D b a) := {t | IsHalf e t ∧ IsSmall P β' β (-(n : ℤ)) t}
  have hSK : ∀ t ∈ S, φ t ∈ K := fun t ht => by
    have h := (hsmall _ t).1 ht.2
    exact Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s
  have hSmallH : ∀ t, IsSmall P β' β n t ↔ φ t ∈ H := fun t => hsmall _ t
  let C : Finset (V ⧸ H) := (Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F).filter
    (fun c => ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c)
  let rep : V ⧸ H → Mx D b a := fun c =>
    if h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c then h.choose else 0
  have hrep : ∀ c ∈ C, rep c ∈ S ∧ ((φ (rep c) : V) : V ⧸ H) = c := by
    intro c hc
    have h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c := (Finset.mem_filter.1 hc).2
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨C.image rep, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    exact (hrep c hc).1
  · intro t ht1 ht2
    have ht : t ∈ S := ⟨ht1, ht2⟩
    obtain ⟨x, hxF, hx⟩ := Set.mem_iUnion₂.1 (hF (hSK t ht))
    have hc : ((φ t : V) : V ⧸ H) ∈ C := by
      have heq : ((x : V) : V ⧸ H) = ((φ t : V) : V ⧸ H) :=
        (QuotientAddGroup.eq_iff_sub_mem).2 (by
          have : φ t - x ∈ H := hx
          simpa using H.neg_mem this)
      have hmem : ((φ t : V) : V ⧸ H) ∈ Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F :=
        Finset.mem_image.2 ⟨x, hxF, heq⟩
      exact Finset.mem_filter.2 ⟨hmem, t, ht, rfl⟩
    refine ⟨rep _, Finset.mem_image.2 ⟨_, hc, rfl⟩, ?_⟩
    rw [hSmallH, hφ]
    exact (QuotientAddGroup.eq_iff_sub_mem).1 (hrep _ hc).2.symm
  · intro r hr r' hr' hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hr'
    rw [hSmallH, hφ] at hs
    have : c = c' := by
      rw [← (hrep c hc).2, ← (hrep c' hc').2]
      exact (QuotientAddGroup.eq_iff_sub_mem).2 hs
    rw [this]

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_ratio_gen {X A : Scheme.{0}} {M : LB X} {L₀ : LB A} (hM : M.IsLB) (hL₀ : L₀.IsLB)
    {K : Type} [Fintype K] (φ : K → (A ⟶ X)) (ε : K → ℤ) (F : A ⟶ X)
    (w : LB.Iso L₀ (LB.LinComb M φ ε)) (hw : w.IsGen) (W : LB.Iso L₀ (M.pull F)) (hW : W.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb M (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (J : (Z ⟶ X) → M.ι) (j' : L₀.ι), Good M z J → r z ∈ L₀.U j' →
        val τ r z J = gv w r z (fun k => J (r ≫ φ k)) j' * (gw W r z (J (r ≫ F)) j')⁻¹ := by
  classical
  have pW := (isGen_iff W).1 hW
  have l1 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (LB.LinComb M φ ε).U (j ∘ Sum.inl) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy.1 (Sum.inl i), hy.2⟩
  have l2 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (M.pull F).U (fun _ => j (Sum.inr PUnit.unit)) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 (Sum.inr PUnit.unit), hy.2⟩
  let u : ∀ (j : K ⊕ PUnit → M.ι) k, Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k)ˣ := fun j k =>
    res (l1 j k) (w.s (j ∘ Sum.inl, k)) * (res (l2 j k) (W.s (fun _ => j (Sum.inr PUnit.unit), k)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k →
      gm r z _ (u j k) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg _ (gm_res r z _ hz _))))
  have rel : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j j' : K ⊕ PUnit → M.ι) (k k' : L₀.ι),
      r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j → r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j' →
      r z ∈ L₀.U k → r z ∈ L₀.U k' →
      gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ =
        trF (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1)) r z j j' *
          (gv w r z (j' ∘ Sum.inl) k' * (gw W r z (j' (Sum.inr PUnit.unit)) k')⁻¹) := by
    intro Z r z j j' k k' hj hj' hk hk'
    have key : ∀ {G : Type} [CommGroup G] (a c d x y : G), a * c⁻¹ * x * (d * c⁻¹ * y)⁻¹ = a * d⁻¹ * (x * y⁻¹) :=
      fun a c d x y => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    have a₁ : r z ∈ (LB.LinComb M φ ε).U (j ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj (Sum.inl i)
    have a₂ : r z ∈ (LB.LinComb M φ ε).U (j' ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj' (Sum.inl i)
    have b₁ : F (r z) ∈ M.U (j (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj (Sum.inr PUnit.unit)
    have b₂ : F (r z) ∈ M.U (j' (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj' (Sum.inr PUnit.unit)
    have e := gm_linComb M φ ε r z _ _ a₁ a₂
    rw [gm_isGen hw r z _ _ k k' a₁ a₂ hk hk', pW Z r z _ _ k k' b₁ b₂ hk hk']
    erw [e]
    rw [trF, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, zpow_neg, zpow_one]
    exact key _ _ _ _ _
  have glue : ∀ j : K ⊕ PUnit → M.ι, ∃ s : Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j)ˣ,
      ∀ k, res (inf_le_left : LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤ _) s = u j k := fun j =>
    glue_unit _ (fun k => LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL₀ y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) (u j)
      (fun k k' y hy => by
        rw [hu _ _ y j k hy.1, hu _ _ y j k' hy.2, rel _ (𝟙 A) y j j k k' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hM _ _ (𝟙 A) y hy.1.1, _root_.one_mul])
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j →
      r z ∈ L₀.U k → gm r z _ (s j) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hj hk => (gm_res r z _ (show r z ∈ _ ⊓ L₀.U k from ⟨hj, hk⟩) (s j)).symm.trans
      ((congrArg (gm r z _) (hs j k)).trans (hu Z r z j k ⟨hj, hk⟩))
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z J j' hJ hj' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL₀ y
    exact (hv _ (𝟙 A) y j k hj hk).trans ((rel _ (𝟙 A) y j j' k k hj hj' hk hk).trans
      (congrArg _ (hv _ (𝟙 A) y j' k hj' hk).symm))
  · exact hv Z r z _ j' (hJ.mem _ r) hj'

end GlobalTheory.MumCmp.TwRatio

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_twist_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  intro R _ _ _ D₀ D β b w hw W hW
  classical
  obtain ⟨τ, hτ, vτ⟩ := exists_ratio_gen D.P.isLB D₀.P.isLB (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε
    (GlobalTheory.MumCmp.twφ D₀ D β b 0) w hw W hW
  obtain ⟨t₀, ht₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]
  have hF : FormEq (Sum.elim (GlobalTheory.MumCmp.twφ D₀ D β b) (fun _ : PUnit => GlobalTheory.MumCmp.twφ D₀ D β b 0))
      (Sum.elim GlobalTheory.MumCmp.twε (fun _ => -1))
      (fun k => D₀.P.A.hom ≫ (![b.left, η[D.P.A].left] : Fin 2 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left)) k)
      ![-1, 1] := by
    intro U _ h
    have e1 : GlobalTheory.MumCmp.twφ D₀ D β b 1 = D₀.P.A.hom ≫ b.left := rfl
    have e2 : GlobalTheory.MumCmp.twφ D₀ D β b 2 = D₀.P.A.hom ≫ η[D.P.A].left := rfl
    rw [Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_two]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, e1, e2, GlobalTheory.MumCmp.twε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen D.P.isLB hF τ hτ
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio D.P.isLB hτ' (DVR.pullGen_isGen _ _ _ t₀ ht₀ D₀.P.A.hom)
  have hG := GlobalTheory.globalFns_holds _ D₀.P.A D₀.P.isAb
  obtain ⟨c, hc⟩ := hG.2 a.val
  obtain ⟨c', hc'⟩ := hG.2 (a⁻¹).val
  have hcc : c * c' = 1 := hG.1 (by rw [map_mul, hc, hc', Units.mul_inv, map_one])
  let cu : Γ(Sp R, ⊤)ˣ := ⟨c, c', hcc, (mul_comm c' c).trans hcc⟩
  have hcu : pullU D₀.P.A.hom ⊤ cu = a := Units.ext hc
  obtain ⟨ν, hν, vν⟩ := GlobalTheory.TorsionTranslate.exists_scale t₀ ht₀ cu
  refine ⟨ν, hν, fun Z r z J j' hJ hj' => ?_⟩
  have e1 := vτ Z r z J j' hJ hj'
  have e2 := vτ' Z r z J hJ
  have e3 := ha Z r z J hJ
  have e4 := val_pull hJ t₀ D₀.P.A.hom r
  have e5 := vν Z (r ≫ D₀.P.A.hom) z J hJ
  have e6 : gm r z ⊤ a = gm (r ≫ D₀.P.A.hom) z ⊤ cu := by
    rw [← hcu]; exact gm_pull r D₀.P.A.hom z ⊤ trivial cu
  rw [e5, ← e6, ← e4, ← e3, e2, e1, mul_left_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.MumCmp.TwRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparison
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TranslLev

open GlobalTheory.MumCmp.Transl UnifCompare

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]


set_option maxHeartbeats 800000 in
theorem exists_iso_translate_levels [IsLocalRing R] (hR : AdmBase R I) (hG : IsSemiAbelian G) {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left →
      ae ≫ (U.gt e).pG.left = thick R I e ≫ b.left)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull (tr a).left)) (hw : wL.IsGen) (β : D'.toPre.P.A ≅ D.toPre.P.A)
    (hβ : ∀ e, (U'.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) :
    ∃ w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left),
      w.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left),
        h ≫ (fstG I e G).left = (fstG I e G).left ≫ (tr a).left →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
          (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
        (tr a).left ((fstG I e G).left (r z)) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
        gw w (r ≫ (U'.gt e).pG.left) z jM jM' * gw (U'.w e) r z jM' (fun _ => jL') =
          gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  rw [isGen_iff] at hw
  obtain ⟨hf, hs⟩ := surjective_appTop U
  obtain ⟨ae, hae⟩ : ∃ ae : ∀ e, 𝟙_ _ ⟶ thickObj R I e G,
      ∀ e, (ae e).left ≫ (fstG I e G).left = thick R I e ≫ a.left :=
    ⟨fun e => Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _), fun e => pullback.lift_fst _ _ _⟩
  let Φ : D'.toPre.P.A ≅ D.toPre.P.A :=
    { hom := β.hom * (toUnit _ ≫ b)
      inv := (𝟙 _ * (toUnit _ ≫ b)⁻¹) ≫ β.inv
      hom_inv_id := by
        rw [← Category.assoc, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
          mul_inv_cancel_right, β.hom_inv_id]
      inv_hom_id := by
        rw [MonObj.comp_mul, Category.assoc, β.inv_hom_id, Category.comp_id, ← Category.assoc, comp_toUnit,
          inv_mul_cancel_right] }
  let βe : ∀ e, thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A := fun e =>
    (Over.pullback (thick R I e)).mapIso Φ
  have hβe : ∀ e, (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left = (fstG I e D'.toPre.P.A).left ≫ Φ.hom.left :=
    fun e => pullback.lift_fst _ _ _
  have hb : ∀ e, (tr (ae e)).left ≫ (U.gt e).pG.left =
      (U'.gt e).q.left ≫ (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left := fun e => by
    have h₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae e) (𝟙 (thickObj R I e G))
    have h₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae e) = toUnit _ ≫ b := by
      apply Over.OverMorphism.ext
      show ((thickObj R I e G).hom ≫ (ae e).left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ b.left
      rw [Category.assoc, Category.assoc]
      exact congrArg ((thickObj R I e G).hom ≫ ·) (hab e _ (Over.w (ae e)) (hae e))
    have h₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U'.gt e).pG ≫ β.hom :=
      Over.OverMorphism.ext ((Category.id_comp _).trans (hβ e).symm)
    have h₄ : (U'.gt e).pG ≫ Φ.hom = ((U'.gt e).pG ≫ β.hom) * (toUnit _ ≫ b) := by
      show (U'.gt e).pG ≫ (β.hom * (toUnit _ ≫ b)) = _
      rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
    rw [h₂, h₃, _root_.mul_comm (toUnit _ ≫ b), ← h₄] at h₁
    rw [hβe]
    exact (congrArg (fun q => q.left) h₁).trans (Category.assoc (U'.gt e).q.left _ _)
  choose v hvg hv using fun e => exists_level (hae e) hw hG ha hf hs β.hom (hβ e) _ (hb e)
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left =
      (βe e).hom.left ≫ thickMap R I e D.toPre.P.A := fun e => thickMap_comm e _ _ _ (hβe e) (hβe (e + 1))
  have ht : ∀ e, thickMap R I e G ≫ (tr (ae (e + 1))).left = (tr (ae e)).left ≫ thickMap R I e G := fun e =>
    thickMap_comm e _ _ _ (tr_fst (hae e)) (tr_fst (hae (e + 1)))
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Ψ, w, hwg, H⟩ := exists_iso_of_compatible_thickenings GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample R I D.toPre.P D'.toPre.P βe v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((βe e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((tr a).left ((fstG I e G).left x))
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left ((tr (ae e)).left x) ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hb e)).mpr (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have k₁ : (thickMap R I e G ≫ (tr (ae (e + 1))).left) ≫ (U.gt (e + 1)).pG.left =
        (tr (ae e)).left ≫ (U.gt e).pG.left :=
      (congrArg (· ≫ (U.gt (e + 1)).pG.left) (ht e)).trans ((Category.assoc _ _ _).trans
        (congrArg ((tr (ae e)).left ≫ ·) (U.gt_q e)))
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) k₁).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => (tr a).left (g x) ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', ht, gw_trans' U e (tr (ae e)).left x j jL hM
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (tr_fst (hae e))).mpr hL), trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have := D'.toPre.P.isAb.proper
  have := D.toPre.P.isAb.proper
  have eΨ : Ψ.hom = padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b) :=
    hom_eq_of_thickenings_of_isProper R I (IsAdicComplete.le_jacobson_bot I) _ _ Ψ.hom Φ.hom
      fun e => (H e).1.trans (hβe e)
  have eΨ' : (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left = Ψ.hom.left := by rw [eΨ]
  rw [eΨ']
  refine ⟨w, hwg, fun e h hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
  have heq : h = (tr (ae e)).left := (cancel_mono (fstG I e G).left).1 (by rw [hh, tr_fst (hae e)])
  subst heq
  have hq : (U'.gt e).pG.left = (U'.gt e).q.left ≫ (fstG I e D'.toPre.P.A).left := rfl
  have m₁ : (fstG I e D.toPre.P.A).left ((βe e).hom.left ((r ≫ (U'.gt e).q.left) z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hb e)).mp a₁
  have m₂ : (fstG I e D'.toPre.P.A).left ((r ≫ (U'.gt e).q.left) z) ∈ D'.toPre.P.L.U jM' :=
    (congrArg (fun g => g (r z) ∈ D'.toPre.P.L.U jM') hq).mp a₂
  have k := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM' m₁ m₂
  have k' : gw w (r ≫ (U'.gt e).pG.left) z jM jM' = gw (v e) (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') :=
    (congrArg (fun g => gw w g z jM jM') (show r ≫ (U'.gt e).pG.left =
      (r ≫ (U'.gt e).q.left) ≫ (fstG I e D'.toPre.P.A).left by rw [hq, Category.assoc])).trans k
  rw [← hv e Z r z jM jM' jL jL' a₁ a₂ a₃ a₄, k']

end GlobalTheory.MumCmp.TranslLev

theorem GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (hwL : wL.IsGen) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left),
    ∃ W : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0)), W.IsGen ∧
      ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D₂.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U₂.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U jM' →
        ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U jL' →
        Geo.Tor.gw W (r ≫ (U₂.gt e).pG.left) z jM jM' * Geo.Tor.gw (U₂.w e) r z jM' (fun _ => jL') =
          Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z jL jL' := by
  intro R _ _ _ hR D A G _ _ hG U a ha b hab A₂ D₂ U₂ wL hwL β hβ
  obtain ⟨W, hW, hv⟩ := GlobalTheory.MumCmp.TranslLev.exists_iso_translate_levels hR.1 hG U.toUnifPre U₂.toUnifPre a ha b
    hab wL hwL β hβ
  exact ⟨W, hW, fun e h _ hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => hv e h hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseAdeleAwayFromPOfUnitCongruencesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_adeleAwayFromP_of_unitCongruences : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ), (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) → ∃ c' : AfP p, c * c' = 1 := by
  first | (exact @GlobalTheory.AfUnit.exists_mul_eq_one) | (exact GlobalTheory.AfUnit.exists_mul_eq_one) | (intros; apply GlobalTheory.AfUnit.exists_mul_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumTrait.exists_unif_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  obtain ⟨p, hp, W₀, hW, i, V₁, _, _, _, ρ₁, b₁, hV₁, hρ₁, hf₁, hl₁, hb₁⟩ := _root_.GlobalTheory.TraitPlace.exists_place_finite_ext R hR E H
  have hpq : 1 ≤ Dm.p + Dm.q := by have := hP.2.1; omega
  let Xo : ∀ l : Level H, Moduli Dm l := fun l => (GlobalTheory.Moduli.moduli_scheme_exists E H Dm l hpq).some
  obtain ⟨Y, hY, -⟩ := (GlobalTheory.partI_of_semistableReduction GlobalTheory.SS.semistableReductionSt).2 E H Dm hpq Xo
  have hFour := ((hY p W₀ hp hW).2 i).2.2
  obtain ⟨V, _, _, _, ρ, b, ϖ, a, hV, hρi, hρf, hϖ, hmatch⟩ := GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR R hR E H Dm D o hX hP i.l i.c _ (i.c.V W₀).subtype
    Subtype.val_injective V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.Mum.exists_point_hasArcData_uniformiser E H Dm i.l (Xo i.l) i.c _ _ (Y p W₀ hp hW i) hFour V hV b ϖ a hϖ
  obtain ⟨t, -, P, hpull⟩ := hmatch (Xo i.l) (Y p W₀ hp hW i) y hy
  exact ⟨V, _, _, _, ρ, P.D, t.G, inferInstance, inferInstance, P.A, hV, hρi, hρf, hpull, t.semi, ⟨P.U⟩,
    GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised V (maximalIdeal V) E H t P⟩
end

