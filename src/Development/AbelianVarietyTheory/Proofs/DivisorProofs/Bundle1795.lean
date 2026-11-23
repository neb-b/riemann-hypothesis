module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycle
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem pbA_comp (M : TwoLevels E r U C) (u v : U) (f : HA M) :
    pbA M v (pbA M u f) = pbA M (u * v) f := by
  apply Subtype.ext
  funext c x
  show f.1 (u • v • c) ⟨lact (M.tr u (v • c)) (lact (M.tr v c) x.1), _⟩ =
    f.1 ((u * v) • c) ⟨lact (M.tr (u * v) c) x.1, _⟩
  rw [show u • v • c = (u * v) • c from (mul_smul u v c).symm]
  have hγ := M.tr_mul u v c
  have hy : lact (M.tr u (v • c) * M.tr v c) x.1 ∈ M.dom := by
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]
    exact lact_tr_mem M u _ (lact_tr_mem M v c x.2)
  have e : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1) =
      lact (M.tr (u * v) c) x.1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel_right]
  have hz : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹)
      (⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ : M.dom).1 ∈ M.dom := by
    show lact _ (lact _ x.1) ∈ M.dom
    rw [e]; exact lact_tr_mem M (u * v) c x.2
  have key := f.2.2 ((u * v) • c) _ hγ ⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ hz
  rw [show (⟨lact (M.tr (u * v) c) x.1, lact_tr_mem M (u * v) c x.2⟩ : M.dom) =
      ⟨lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1), hz⟩
      from Subtype.ext e.symm, key]
  exact congrArg (f.1 _) (Subtype.ext (ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul _ _ _).symm)

theorem pbA_one (M : TwoLevels E r U C) (f : HA M) : pbA M 1 f = f := by
  apply Subtype.ext
  funext c x
  show f.1 ((1 : U) • c) ⟨lact (M.tr 1 c) x.1, _⟩ = f.1 c x
  have hγ := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at hγ
  rw [mul_inv_rev, mul_inv_cancel_left] at hγ
  have hz : lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) ∈ M.dom := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    exact x.2
  have key := f.2.2 c _ hγ ⟨lact (M.tr 1 c) x.1, lact_tr_mem M 1 c x.2⟩ hz
  simp only [one_smul]
  rw [← key]
  refine congrArg (f.1 c) (Subtype.ext ?_)
  show lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) = x.1
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]

theorem tw_law (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (a : U → C → ℂˣ) (ha : ∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) :
    tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧
      ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) =
        tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  refine ⟨?_, fun u v => ?_⟩
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ 1 (Polynomial.C f) = Polynomial.C f
      rw [tw_C, pbA_one]
    · show tw M _ 1 Polynomial.X = Polynomial.X
      rw [tw_X]
      have h1 : cst M (fun c => (a 1 c : ℂ)) = 1 := by
        apply Subtype.ext
        funext c x
        show (a 1 c : ℂ) = 1
        have h := ha 1 1 c
        rw [one_mul, one_smul] at h
        have h' : a 1 c = 1 := by
          have := congrArg (fun t => (a 1 c)⁻¹ * t) h
          simpa using this.symm
        rw [h', Units.val_one]
      rw [h1, map_one, one_mul]
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ v (tw M _ u (Polynomial.C f)) = tw M _ (u * v) (Polynomial.C f)
      rw [tw_C, tw_C, tw_C, pbA_comp]
    · show tw M _ v (tw M _ u Polynomial.X) = tw M _ (u * v) Polynomial.X
      rw [tw_X, map_mul, tw_C, tw_X, tw_X, ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      apply Subtype.ext
      funext c x
      show (a u (v • c) : ℂ) * (a v c : ℂ) = (a (u * v) c : ℂ)
      rw [ha v u c, Units.val_mul, mul_comm]

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariant
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isSec_cast (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (h1 : X.Ψ = Ψ) (h2 : X.Gm = Gm) (h3 : X.p0 = p0) (la : Wt Ψ r) (G : Frame Ψ r → ℂ)
    (hG : X.IsSec (castWt h1 la) (fun x => G (castFrame h1 x))) :
    DifferentiableOn ℂ G (GG Ψ Gm p0) ∧
      ∀ γ ∈ X.Γ, ∀ x ∈ GG Ψ Gm p0, G (lact γ x) = X.χ (castWt h1 la) γ * G x := by
  subst h1 h2 h3
  exact ⟨hG.1, hG.2.2⟩

theorem res_mem_HA (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) : M.res F ∈ HA M := by
  have key := fun c => isSec_cast (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c) la (F c)
    (hF c).1.1
  refine ⟨fun c => ⟨F c, (key c).1, fun x => rfl⟩, fun c γ hγ x hx => ?_⟩
  show F c (lact γ x.1) = F c x.1
  rw [(key c).2 γ hγ x.1 x.2, M.χ_one c _ γ hγ, one_mul]

end GlobalTheory.CuspEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalf
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipModHalf

theorem zpow_sub_one_eq_mul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (ℓ : A ≃ₗ[R] A) (n : ℤ) :
    ∃ X : Module.End R A, Commute ((ℓ : Module.End R A) - 1) X ∧
      ((ℓ ^ n : A ≃ₗ[R] A) : Module.End R A) - 1 = ((ℓ : Module.End R A) - 1) * X := by
  have h1 : (ℓ.symm : Module.End R A) * (ℓ : Module.End R A) = 1 := by
    ext y; simp
  have h2 : (ℓ : Module.End R A) * (ℓ.symm : Module.End R A) = 1 := by
    ext y; simp
  have hDℓ : Commute ((ℓ : Module.End R A) - 1) (ℓ : Module.End R A) :=
    (Commute.refl _).sub_left (Commute.one_left _)
  have hDs : Commute ((ℓ : Module.End R A) - 1) (ℓ.symm : Module.End R A) := by
    show _ = _
    rw [sub_mul, mul_sub, h2, h1, one_mul, mul_one]
  induction n using Int.induction_on with
  | zero => exact ⟨0, Commute.zero_right _, by ext y; simp⟩
  | succ k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ : Module.End R A) * X + 1, (hDℓ.mul_right hc).add_right (Commute.one_right _), ?_⟩
    have e : ((ℓ ^ ((k : ℤ) + 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ : Module.End R A) * ((ℓ ^ (k : ℤ) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [add_comm, zpow_add, zpow_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    noncomm_ring
  | pred k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ.symm : Module.End R A) * X - (ℓ.symm : Module.End R A),
      (hDs.mul_right hc).sub_right hDs, ?_⟩
    have e : ((ℓ ^ (-(k : ℤ) - 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ.symm : Module.End R A) * ((ℓ ^ (-(k : ℤ)) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [sub_eq_neg_add, zpow_add, zpow_neg_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    set s : Module.End R A := (ℓ.symm : Module.End R A)
    set l : Module.End R A := (ℓ : Module.End R A)
    have : s * ((l - 1) * X + 1) - 1 = (l - 1) * (s * X - s) + (s * l - 1) * X
        - (l * s - 1) * X + (l * s - 1) := by noncomm_ring
    rw [this, h1, h2]; simp

end GlobalTheory.UnipModHalf

namespace GlobalTheory.UnipModHalf

open Matrix

theorem unip_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  intro E _ _ r L' Mb P hMP A _ _ φ ℓ n hℓ γ t hγ hγ1 ht w hw

  let tL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin t).restrictScalars (𝓞 E)
  let gL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin γ).restrictScalars (𝓞 E)
  let T : Module.End (𝓞 E) L' := tL.restrict (fun x hx => (ht ⟨x, hx⟩).1)
  let G : Module.End (𝓞 E) L' := gL.restrict (fun x hx => hγ x hx)
  let U : Module.End (𝓞 E) L' := G * T - 1
  have hU : ∀ x : L', ((U x : L') : Fin r → E) = γ *ᵥ (t *ᵥ (x : Fin r → E)) - x := by
    intro x; rfl
  have hpow : ∀ k : ℕ, ∀ x : L', ((γ * t - 1) ^ k) *ᵥ (x : Fin r → E) = (((U ^ k) x : L') : Fin r → E) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply, hU,
        Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

  have hsub : ∀ (I : Ideal (𝓞 E)) (z : L'), (z : Fin r → E) ∈ I • L' → z ∈ I • (⊤ : Submodule (𝓞 E) L') := by
    intro I z hz
    have e : I • L' = (I • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [e] at hz
    obtain ⟨u, hu, huz⟩ := hz
    have : u = z := Subtype.ext huz
    exact this ▸ hu
  set ℓn : Module.End (𝓞 E) A := ((ℓ ^ n : A ≃ₗ[𝓞 E] A) : Module.End (𝓞 E) A)
  have hπU : ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (U x) = φ ((ℓn - 1) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro x
    have hG : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (G (T x)) = (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hsub Mb _ (hγ1 _ (T x).2)
    have hT : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) = φ ((ℓ ^ n) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := (ht x).2
    simp only [U, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, map_sub, hG, hT]
    simp [ℓn]
  have hπUk : ∀ k : ℕ, ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ k) x) = φ (((ℓn - 1) ^ k) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, hπU, ih, LinearEquiv.symm_apply_apply, pow_succ',
        Module.End.mul_apply]

  obtain ⟨X, hc, hX⟩ := zpow_sub_one_eq_mul ℓ n
  have hℓ' : ∀ y : A, ((ℓn - 1) ^ r) y ∈ P • (⊤ : Submodule (𝓞 E) A) := by
    intro y
    rw [show ℓn - 1 = ((ℓ : Module.End (𝓞 E) A) - 1) * X from hX, hc.mul_pow, Module.End.mul_apply]
    have := hℓ ((X ^ r) y)
    rwa [← Module.End.one_eq_id] at this

  have hQ : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ r) ⟨w, hw⟩) ∈ P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) := by
    rw [hπUk]
    have hm : ((P • (⊤ : Submodule (𝓞 E) A)).map (φ : A →ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))) ≤ P • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hm (Submodule.mem_map_of_mem (hℓ' _))
  have hL : (U ^ r) ⟨w, hw⟩ ∈ P • (⊤ : Submodule (𝓞 E) L') := by
    have e : P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) = (P • (⊤ : Submodule (𝓞 E) L')).map (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [e] at hQ
    have hQ' := Submodule.mem_comap.mpr hQ
    rw [Submodule.comap_map_mkQ] at hQ'
    have hle : Mb • (⊤ : Submodule (𝓞 E) L') ≤ P • (⊤ : Submodule (𝓞 E) L') := Submodule.smul_mono_left hMP
    exact (sup_le hle le_rfl) hQ'
  have key := hpow r ⟨w, hw⟩
  simp only at key
  rw [key]
  have e : P • L' = (P • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [e]
  exact Submodule.mem_map_of_mem hL

end GlobalTheory.UnipModHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorEqOneOfCongruentOne
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead.CongOneChar

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem hat_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) :
    x ∈ hatId D J := by
  refine AddSubgroup.closure_mono ?_ hx
  rintro _ ⟨b, hb, t, ht, rfl⟩
  exact ⟨b, h hb, t, ht, rfl⟩

theorem hat_int {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) : x ∈ OhE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, -, t, ht, rfl⟩ := hy
    exact mul_mem (inc_int b) ht
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | neg a _ ha => exact neg_mem ha

theorem toE_surj (z : EAf D) : ∃ y, toE D y = z := by
  obtain ⟨w, -, hw⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj z
  exact ⟨finQ D w, by rw [toE_finQ, hw]⟩

theorem toE_inj : Function.Injective (toE D) := fun _ _ h =>
  (GlobalTheory.BotFormula.toAfE D).injective ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h)

theorem rho_one_add (Q : Formalism.L2.DIV.Pl D.host.E) {a b : Formalism.MainNotions.StandardLatticesGL3.AE D} (ha : a ∈ OhE D) (hb : b ∈ OhE D)
    (hu : 1 + a * b ∈ OhE D) (h0 : rho Q ⟨a, ha⟩ * rho Q ⟨b, hb⟩ = 0) : rho Q ⟨_, hu⟩ = 1 := by
  have e : (⟨_, hu⟩ : OhE D) = 1 + ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
  rw [e, RingHom.map_add (f := _), RingHom.map_mul, h0, RingHom.map_one, add_zero]

theorem exists_inv {u : Formalism.MainNotions.StandardLatticesGL3.AE D} (hu : u ∈ OhE D) (h : ∀ Q : Formalism.L2.DIV.Pl D.host.E, rho Q ⟨u, hu⟩ ≠ 0) :
    ∃ v ∈ OhE D, u * v = 1 := by
  have hU : IsUnit (⟨toE D u, (toE_int_iff u).2 hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) :=
    Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm _ fun Q => h Q
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  obtain ⟨v, hv⟩ := toE_surj (w : EAf D)
  refine ⟨v, (toE_int_iff v).1 (hv ▸ w.2), toE_inj ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, hv]
  exact congrArg Subtype.val hw


set_option maxHeartbeats 1000000 in
theorem unitChar_cong : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {k : ℕ} (P : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, (P - 1) i j ∈ hatId D 𝔪) →
  unitChar ν e (P.map (toE D)) = 1 := by
  intro D e 𝔪 hG ν hK k P hP
  have hm1 := one_sub_eps_mod hG
  obtain ⟨S, c, he, hc, h𝔪, -⟩ := hG
  have hO := eps_int he
  have h2 := eps_conj he
  have hte := toE_finQ e
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => by
    have h1 : (1 : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h3 := add_mem (hat_int (hP i j)) h1
    rwa [Matrix.sub_apply, sub_add_cancel] at h3
  have hm := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of P hPO hP
  have hdet : (P.map (toE D)).det = toE D P.det := (RingHom.map_det (toE D) _).symm
  have hmO := hat_int hm
  have huO : 1 + finQ D e * (P.det - 1) ∈ OhE D := add_mem (one_mem _) (mul_mem hO hmO)
  obtain ⟨v, hvO, huv⟩ := exists_inv huO fun Q => by
    have := Q.isPrime
    have h0 : rho Q ⟨_, hO⟩ * rho Q ⟨_, hmO⟩ = 0 := by
      by_cases hQ : Q ∈ S
      · have hle : 𝔪 ≤ Q.asIdeal := by
          rw [h𝔪]
          exact (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => w.asIdeal ^ c w) hQ)).trans
            (Ideal.pow_le_self (hc Q hQ).ne')
        obtain ⟨_, h5⟩ := rho_hat Q (hat_mono hle hm)
        rw [h5, mul_zero]
      · have h5 : rho Q ⟨_, hO⟩ = Formalism.L2.DIV.resS D.host.F Q ⟨_, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he⟩ :=
          congrArg (Formalism.L2.DIV.resS D.host.F Q) (Subtype.ext hte)
        rw [h5, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.res_off he _ hQ, zero_mul]
    have h6 : rho Q ⟨_, huO⟩ = 1 := rho_one_add Q hO hmO huO h0
    rw [h6]
    exact one_ne_zero
  have hm' := hat_mul hm (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1)
  rw [map_sub, map_one] at hm'
  have hm'' := GlobalTheory.FunObj.StdDatum.mul_mem_hatId hO hm'
  generalize finQ D e = ε at hO h2 hte huO huv hm''
  generalize P.det = d at hdet huO huv hm''
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := ⟨_, _, huv, by rw [mul_comm, huv]⟩
  have hyv : (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 + ε * (d - 1) := rfl
  have hyi : ((y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = v := rfl
  obtain ⟨x, hx, hx1, hx2⟩ := exists_finIdl y
  have hU : IsUnitDet e (P.map (toE D)) x := by
    refine ⟨hx.1, ?_, ?_⟩
    · rw [hx1, show (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * d by rw [hyv]; ring, hdet, RingHom.map_add (f := _), RingHom.map_sub,
        RingHom.map_mul, RingHom.map_one, hte]
    · rw [hx2, toE_int_iff, hyi]
      exact hvO
  have hν : ν x = 1 := hK x y hx ⟨huO, hvO⟩ (by
    convert hm'' using 1
    rw [hyv]
    linear_combination (d - 1) * h2)
  rw [unitChar_eq ν e _ hU, hν, inv_one, Circle.coe_one]

end GlobalTheory.StdRead.CongOneChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContraction
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteLevel

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_comb_colP {r : ℕ} (X : Data E r) (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (v : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, v = ∑ a, K a • X.colP x τ a := by
  refine ⟨fun a => ((mat x τ)⁻¹ *ᵥ v) (Fin.castLE X.p0_le a), ?_⟩
  have h1 : v = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  have h2 : ∀ w : Fin r → ℂ, mat x τ *ᵥ w = ∑ j, w j • ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j := by
    intro w; funext k; simp [Matrix.mulVec, dotProduct, ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_apply, mul_comm]
  conv_lhs => rw [h1, h2]
  exact (Fintype.sum_equiv (finCongr hp) _ _ (fun a => rfl)).symm

theorem maj_mulVec_of_definite {r : ℕ} (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v)
    (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ (((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ u) = X.maj x τ u := by
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg' : ∀ w, g *ᵥ (g' *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hg'g : ∀ w, g' *ᵥ (g *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hiso := GlobalTheory.MajInv.hermC_stab X hγ τ.1
  have key := MajorantConjugateTransfer.maj_transfer X hx hx τ g g' hgg' hiso ?_ ?_ (g *ᵥ u)
  · rwa [hg'g] at key
  · intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · exact exists_comb_colP X hp x τ (hx τ).1 _
  · intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · obtain ⟨L, hL⟩ := exists_comb_colP X hp x τ (hx τ).1 (g' *ᵥ X.colP x τ a)
      refine ⟨L, ?_⟩
      calc X.colP x τ a = g *ᵥ (g' *ᵥ X.colP x τ a) := (hgg' _).symm
        _ = g *ᵥ ∑ c, L c • X.colP x τ c := by rw [hL]
        _ = ∑ c, L c • (g *ᵥ X.colP x τ c) := by
          rw [Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul]

theorem eq_one_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g →
    (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) →
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∀ γ ∈ G, γ = 1 := by
  intro E _ _ _ r X G g hg hgr hU hUn hp x hx hnc γ hγ
  refine _root_.GlobalTheory.SmallElement.smallElement E r X g hg hgr G hU hUn x hx hnc γ hγ fun τ u => ?_
  rw [maj_mulVec_of_definite X.toData hp hx γ (hU γ hγ).1 τ u]
  have h0 := MajorantConjugateTransfer.maj_nonneg X.toData hx τ u
  have h1 : 1 ≤ Real.exp (1 / (3 * (r : ℝ))) := Real.one_le_exp (by positivity)
  exact le_mul_of_one_le_left h0 (one_le_pow₀ h1)

end GlobalTheory.DefiniteLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVWStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityV.locality | exact GlobalTheory.WeilLocalityV.locality | (intros; apply GlobalTheory.WeilLocalityV.locality <;> assumption)
end

