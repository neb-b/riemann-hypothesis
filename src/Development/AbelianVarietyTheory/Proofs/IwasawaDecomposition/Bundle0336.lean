module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem formsExport_eq : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  intro D S In T hE hfg hst sd rho hrho he Pq wt i j b h1 h2
  let i' : T.Tw := i
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  let e : (KT D T i' b ⊗[S.Ks] ↥(WKr D S j)) ≃ₗ[KT D T i' b] (KT D T i' b ⊗[S.Ks] ↥(S.A j).WK) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (KT D T i' b) (KT D T i' b)) (LinearEquiv.ofEq _ _ hW)
  have he1 : ∀ (a : KT D T i' b) (w : ↥(WKr D S j)), e (a ⊗ₜ[S.Ks] w) = a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW w) :=
    fun a w => rfl
  have hbc : ∀ (f : Module.End S.Ks ↥(WKr D S j)) (f' : Module.End S.Ks ↥(S.A j).WK),
      (∀ w, ((f w : ↥(WKr D S j)) : S.WL j) = (f' (LinearEquiv.ofEq _ _ hW w) : S.WL j)) →
      ∀ y, e (Module.End.baseChangeHom S.Ks (KT D T i' b) _ f y) = Module.End.baseChangeHom S.Ks (KT D T i' b) _ f' (e y) := by
    intro f f' hf y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a w =>
      show a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW (f w)) = a ⊗ₜ[S.Ks] (f' (LinearEquiv.ofEq _ _ hW w))
      exact congrArg (a ⊗ₜ[S.Ks] ·) (Subtype.ext (hf w))
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]
  have hc : ∀ g', cR D S In.chi j g' = chiL S j (In.chi j h1 h2) g' := fun g' => dif_pos ⟨h1, h2⟩
  have hsm : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(WKr D S j)),
      e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e y := fun r y => e.map_smul _ y
  have hsm' : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(S.A j).WK),
      e.symm ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e.symm y := fun r y => e.symm.map_smul _ y
  refine ⟨e, ?_, ?_, ?_⟩
  · let eO : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b :=
      { toFun := fun y => e y, map_add' := fun y z => e.map_add y z, map_smul' := fun r y => hsm r y }
    let eO' : Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b :=
      { toFun := fun y => e.symm y, map_add' := fun y z => e.symm.map_add y z, map_smul' := fun r y => hsm' r y }
    have hle1 : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ≤ (Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b).comap eO := by
      show BsupT D T S i' j b ≤ _
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨LinearEquiv.ofEq _ _ hW w, hw, rfl⟩ : _ ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b)
    have hle2 : Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b ≤ ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b).comap eO' := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨(LinearEquiv.ofEq _ _ hW).symm w, hw, rfl⟩ : _ ∈ BsupT D T S i' j b)
    intro x
    refine ⟨fun hx => hle1 hx, fun hx => ?_⟩
    have h := hle2 hx
    rw [Submodule.mem_comap] at h
    change e.symm (e x) ∈ _ at h
    exact Eq.mp (congrArg (fun (z : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b) => z ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b) (e.symm_apply_apply x)) h
  · intro g x
    change e ((actEndT D T S In.rho In.chi i' j b (S.eG.symm g)) x) =
      (actEnd ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b (In.rho j h1 h2) (In.chi j h1 h2) (S.eG.symm g)) (e x)
    change e ((readK D T i' b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g)) x) =
      (readK D T i' b (chiL S j (In.chi j h1 h2) (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (e x)
    rw [LinearEquiv.map_smul, hbc _ (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl) x, hc]
  · intro k P x
    change e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (hLr D S In j k P) x) =
      (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK
          (((In.hL j k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK)
            fun x hx => In.hs j h1 h2 k P x hx) (e x)
    rw [LinearEquiv.map_smul, hbc _ _ ?_ x]
    intro w
    rw [hLr, dif_pos ⟨h1, h2⟩]
    rfl

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

theorem readT_integral (i : T.Tw) (b : Bool) (x : ↥D.LL0) (hx : IsIntegral ℤ x) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = readT D T i b x := by
  have key : ∀ e : ↥D.LL0 →+* FractionRing (T.O0 i),
      ∃ y : T.O0 i, algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = e x := by
    intro e
    have h1 : IsIntegral ℤ (e x) := by
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨p, hp, ?_⟩
      have h3 := congrArg e hpx
      rw [map_zero, Polynomial.hom_eval₂] at h3
      rwa [RingHom.ext_int (e.comp (algebraMap ℤ _)) (algebraMap ℤ _)] at h3
    have h2 : IsIntegral (T.O0 i) (e x) := h1.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  obtain ⟨y, hy⟩ := key (if b then T.emb0 i else T.emb0b i)
  refine ⟨algebraMap (T.O0 i) (T.O i) y, ?_⟩
  unfold readT
  rw [RingHom.comp_apply, ← hy]
  exact (IsLocalization.map_eq _ _).symm

theorem ksInt_mem (i : T.Tw) (b : Bool) (a : 𝓞 S.Ks) :
    ∃ o : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) o = algebraMap S.Ks (KT D T i b) (a : S.Ks) :=
  readT_integral D T i b _ ((RingOfIntegers.isIntegral_coe a).map S.kKs.toIntAlgHom)

theorem one_tmul_smul (i : T.Tw) (j : ℕ) (b : Bool) (c : S.Ks) (m : ↥(WKr D S j)) :
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (c • m) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
      algebraMap S.Ks (KT D T i b) c • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]

theorem fmT_eq_zero (i : T.Tw) (j : ℕ) (b : Bool) (h : ¬ (1 ≤ j ∧ j ≤ D.R.m)) (z : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul k m =>
    have hm : m = 0 := by
      exact Subtype.ext (Submodule.mem_bot _ |>.mp ((WKr_off D S h).le m.2))
    rw [hm, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem bsupT_fg_span (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) :
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m
  swap
  · have hz := fmT_eq_zero D T S i j b h
    refine ⟨?_, ?_⟩
    · have : BsupT D T S i j b = ⊥ := (Submodule.eq_bot_iff _).mpr fun z _ => hz z
      rw [this]; exact Submodule.fg_bot
    · exact Submodule.eq_top_iff'.mpr fun z => by rw [hz z]; exact Submodule.zero_mem _
  obtain ⟨T0, hT, hMK, hWK⟩ := In.mk_fg j h.1 h.2
  have hmem : ∀ t ∈ T0, t ∈ WKr D S j := fun t ht => by
    rw [WKr_of D S h.1 h.2]; exact (hMK t (hT t ht)).1
  let g : ↥T0 → FmT D T S i j b := fun t =>
    ((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨t.1, hmem t.1 t.2⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j))
  have hgB : Set.range g ⊆ BsupT D T S i j b := by
    rintro _ ⟨t, rfl⟩
    exact Submodule.subset_span ⟨⟨t.1, hmem t.1 t.2⟩, hT t.1 t.2, rfl⟩

  have hO : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (T.O i) (Set.range g) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul a y _ hy =>
      have hay : a • y = (a : S.Ks) • y := (algebraMap_smul S.Ks a y).symm
      have hm : a • y ∈ WKr D S j := by rw [hay]; exact Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨a • y, hy'⟩ : ↥(WKr D S j)) = (a : S.Ks) • ⟨y, hy.1⟩ := Subtype.ext hay
      rw [this, one_tmul_smul]
      obtain ⟨o, ho⟩ := ksInt_mem D T S i b a
      rw [← ho]
      exact Submodule.smul_mem _ o (hy.2 hy.1)
  have hBeq : BsupT D T S i j b = Submodule.span (T.O i) (Set.range g) := by
    refine le_antisymm ?_ (Submodule.span_le.mpr hgB)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hO x.1 (hMK x.1 hx).2).2 x.2
  refine ⟨?_, ?_⟩
  · rw [hBeq]; exact Submodule.fg_span (Set.finite_range g)

  have hK : ∀ y ∈ Submodule.span S.Ks (T0 : Set (S.WL j)), y ∈ WKr D S j ∧ ∀ hy : y ∈ WKr D S j,
      (((1 : KT D T i b) ⊗ₜ[S.Ks] (⟨y, hy⟩ : ↥(WKr D S j)) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) : FmT D T S i j b) ∈
        Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨hmem t ht, fun _ => Submodule.subset_span (hgB ⟨⟨t, ht⟩, rfl⟩)⟩
    | zero =>
      refine ⟨Submodule.zero_mem _, fun hy => ?_⟩
      have : (⟨0, hy⟩ : ↥(WKr D S j)) = 0 := rfl
      rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨Submodule.add_mem _ hy.1 hz.1, fun hyz => ?_⟩
      have : (⟨y + z, hyz⟩ : ↥(WKr D S j)) = ⟨y, hy.1⟩ + ⟨z, hz.1⟩ := rfl
      rw [this, TensorProduct.tmul_add]
      exact Submodule.add_mem _ (hy.2 hy.1) (hz.2 hz.1)
    | smul c y _ hy =>
      have hm : c • y ∈ WKr D S j := Submodule.smul_mem _ _ hy.1
      refine ⟨hm, fun hy' => ?_⟩
      have : (⟨c • y, hy'⟩ : ↥(WKr D S j)) = c • ⟨y, hy.1⟩ := rfl
      rw [this, one_tmul_smul]
      exact Submodule.smul_mem _ _ (hy.2 hy.1)
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at z
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul k m =>
    have hm : (m : S.WL j) ∈ Submodule.span S.Ks (T0 : Set (S.WL j)) := by
      exact hWK _ ((WKr_of D S h.1 h.2).le m.2)
    have h1 := (hK m.1 hm).2 m.2
    have h2 : (k ⊗ₜ[S.Ks] m : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = k • ((1 : KT D T i b) ⊗ₜ[S.Ks] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ k h1
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem bsupT_fg_span_all : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ :=
  fun D S In T i j b => bsupT_fg_span D T S In i j b

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section Transport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem bc_mem_range_intL_of (φ : K →+* K) (hφ : ∀ x ∈ intL K, φ x ∈ intL K) {n : ℕ}
    (x : GL (Fin n) K) (hx : x ∈ (bc (n := Fin n) (intL K).subtype).range) :
    bc (n := Fin n) φ x ∈ (bc (n := Fin n) (intL K).subtype).range := by
  obtain ⟨M, rfl⟩ := hx
  refine ⟨bc (φ.restrict (intL K) (intL K) hφ) M, ?_⟩
  apply Units.ext
  ext i j
  simp [bc]

theorem guMap_symm_comp (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) {n : ℕ} (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [guMap_val]

theorem mem_KU_iff_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} (y : GU σ n) :
    y ∈ KU σ n ↔ guMap g hg n y ∈ KU σ' n := by
  have hs : ∀ x ∈ intL K, (g.symm : K →+* K) x ∈ intL K := by
    intro x hx
    rw [hint]
    simpa using hx
  simp only [KU, intPts, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨(guMap g hg n y).2, bc_mem_range_intL_of (g : K →+* K) (fun x hx => (hint x).1 hx) _ h⟩
  · rintro ⟨-, h⟩
    refine ⟨y.2, ?_⟩
    have := bc_mem_range_intL_of (g.symm : K →+* K) hs _ h
    convert this using 1
    apply Units.ext
    ext i j
    simp [bc, guMap_val]

end Transport


open Classical in
theorem satU_guMap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q n m h' hbi hcond α
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : GU σ n ≃* GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have he : ∀ y, e y = guMap g hg n y := fun _ => rfl
  let E : GU σ n ⧸ KU σ n ≃ GU σ' n ⧸ KU σ' n :=
    Quotient.congr e.toEquiv (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
      change a⁻¹ * b ∈ KU σ n ↔ (e a)⁻¹ * e b ∈ KU σ' n
      rw [← map_inv, ← map_mul, he]
      exact mem_KU_iff_guMap g hg hint _)
  unfold SatU
  refine finsum_congr (fun a => ?_)
  congr 1
  set F' : GU σ' n → ℂ := fun y => if ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) then h' y else 0 with hF'
  have hinv : ∀ (y : GU σ' n) (k : KU σ' n), F' (y * k) = F' y := by
    intro y k
    simp only [hF']
    have hc : (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔
        (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      constructor
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n)⁻¹, (KU σ' n).mul_mem hk' ((KU σ' n).inv_mem k.2), ?_⟩
        have h1 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((((k : GU σ' n)⁻¹ : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp [Matrix.mul_assoc]
        rw [h1, hy]
        simp [Matrix.mul_assoc]
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n), (KU σ' n).mul_mem hk' k.2, ?_⟩
        simp only [Subgroup.coe_mul, Units.val_mul, hy, Matrix.mul_assoc]
    have hh : h' (y * k) = h' y := by
      have := hbi 1 k y
      simpa using this
    simp only [hc, hh]
  have hmk : ∀ x : GU σ n ⧸ KU σ n, F' (E x).out = F' (guMap g hg n x.out) := by
    intro x
    have hx : E x = QuotientGroup.mk (guMap g hg n x.out) := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ' n) (guMap g hg n x.out)
    rw [hx, hk, hinv]
  calc (∑ᶠ x : GU σ n ⧸ KU σ n, if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((k : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        then h' (guMap g hg n x.out) else 0)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, F' (E x).out := by
        refine finsum_congr (fun x => ?_)
        rw [hmk, hF']
        simp only [hcond a x.out]
    _ = ∑ᶠ x' : GU σ' n ⧸ KU σ' n, F' x'.out := finsum_comp_equiv E (f := fun x' => F' x'.out)

end GlobalTheory.SatInd
end
end

