module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiMapOfTensorPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section

namespace GlobalTheory.EtC.SemiTens

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.map f z) = Sec.map f (Sec.res g z) := by
  have := congrArg (fun k => k.hom z) (f.hom.naturality g.op)
  simpa using this.symm

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (z : Sec F U) :
    Sec.map (0 : F ⟶ G) z = 0 := by
  first
  | rfl
  | (show ((0 : F ⟶ G).hom.app (op U)).hom z = 0
     rw [Sheaf.Hom.zero_hom]; rfl)
  | (simp [Sec.map, Sheaf.zero_val])

variable {Q : ℕ} {R : Type} [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R}

def pairHom (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →+ Sec (J.X t) U →+ Sec (K'.X w) U :=
  AddMonoidHom.mk' (fun a => ((ν.mul U s t w h (ρ₁.app U s a)).toAddMonoidHom).comp (ρ₂.app U t))
    (fun a₁ a₂ => by ext b; simp)

theorem pairHom_smul (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (r : ULift.{1} (ZMod Q)) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    pairHom ν ρ₁ ρ₂ U s t w h (r • a) b = pairHom ν ρ₁ ρ₂ U s t w h a (r • b) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ULift.{1} (ZMod Q)) = r :=
    ⟨(r.down.cast : ℤ), ULift.ext (by change ((r.down.cast : ℤ) : ZMod Q) = r.down; exact ZMod.intCast_zmod_cast _)⟩
  simp [pairHom, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply]

def bmap (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →+ Sec (K'.X w) U := by
  classical
  exact DirectSum.toAddMonoid fun p =>
    TensorProduct.liftAddHom (pairHom ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2) (pairHom_smul ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2)

theorem bmap_of (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    bmap ν ρ₁ ρ₂ U w (DirectSum.of _ p (a ⊗ₜ b)) = ν.mul U p.1.1 p.1.2 w p.2 (ρ₁.app U _ a) (ρ₂.app U _ b) := by
  unfold bmap
  rw [DirectSum.toAddMonoid_of]
  simp [pairHom]

theorem lift_of (τ : Pair I J T) (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.of _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.toModule_lof]
  simp

theorem tensRes_of {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p (a ⊗ₜ b)) = DirectSum.of _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  unfold Tens.res
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.lmap_lof]
  simp [DirectSum.lof_eq_of]

theorem bmap_nat (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (bmap ν ρ₁ ρ₂ U w x) = bmap ν ρ₁ ρ₂ V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [bmap_of, tensRes_of, bmap_of, ν.nat, ρ₁.nat, ρ₂.nat]
    | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add (f := _)] using e
  | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add (f := _)] using e

end GlobalTheory.EtC.SemiTens

namespace GlobalTheory.EtC


open SemiTens in
theorem semiMap_of_tensorPair : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T),
    τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K',
    ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  intro Q R _ I J T I' J' K' τ hτ ν ρ₁ ρ₂
  have H := fun w => _root_.GlobalTheory.EtC.tens_fam (ZMod Q) R τ hτ w (K'.X w) (fun U => bmap ν ρ₁ ρ₂ U w)
    (fun V U g x => bmap_nat ν ρ₁ ρ₂ g w x)
  choose φ hnat hlift using H
  have hmul : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      φ w U (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
    intro U s t w h a b
    have := hlift w U (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))
    rw [lift_of, bmap_of] at this
    exact this
  have key : ∀ (V : Scheme.{0}) (s : ℤ) (x : Tens I J V s),
      Sec.map (K'.d s (s + 1)) (bmap ν ρ₁ ρ₂ V s x) = φ (s + 1) V (Sec.map (T.d s (s + 1)) (τ.lift V s x)) := by
    intro V s x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        obtain ⟨⟨s₁, t₁⟩, hp⟩ := p
        rw [bmap_of, lift_of, ν.leibniz, τ.leibniz, map_add (f := _), Units.smul_def, Units.smul_def, map_zsmul, hmul, hmul,
          ρ₁.comm, ρ₂.comm]
      | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add (f := _)] using e
    | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add (f := _)] using e
  refine ⟨⟨fun U w => φ w U, fun g w a => hnat w _ _ g a, ?_⟩, hmul⟩
  intro U s t y
  by_cases hst : (ComplexShape.up ℤ).Rel s t
  · have ht : t = s + 1 := hst.symm
    subst ht
    apply (_root_.GlobalTheory.EtC.sec_ext_glue R (K'.X (s + 1)) U).1
    obtain ⟨S, hS, hP⟩ := hτ.1 U s y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    rw [res_map, hnat, ← hx, hlift, key, hnat, res_map, ← hx]
  · rw [T.shape s t hst, K'.shape s t hst, map_zero', map_zero', map_zero]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemidirectCharacterExtOfStable
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.StableExt

theorem isSSRep_of_finite {G : Type} [Group G] [Finite G] {d : ℕ} (ρ : G →* GL (Fin d) ℂ) :
    Formalism.MainNotions.N.IsSSRep ρ := by
  haveI : (⊥ : Subgroup G).FiniteIndex := inferInstance
  apply GlobalTheory.FiniteIndexSemisimple.isSSRep_of_finiteIndex ρ (⊥ : Subgroup G)
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine ⟨W', fun g v hv => ?_, hW'⟩
  have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hg, map_one, Units.val_one, Matrix.one_mulVec]
  exact hv

theorem commute_aeval {n : ℕ} {M B : Matrix (Fin n) (Fin n) ℂ} (h : Commute M B) (p : ℂ[X]) :
    Commute M (aeval B p) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

theorem exists_ext : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) →
    ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  intro G Γ _ _ _ _ φ s hs Y hY hYs
  obtain ⟨d, ρ, hρ⟩ := (GlobalTheory.BI.matrixChar_iff_isChar G Y).mpr hY
  let ρ' : G →* GL (Fin d) ℂ := ρ.comp (φ s).toMonoidHom
  obtain ⟨A, hA⟩ := GlobalTheory.TraceConj.conj_of_trace_eq G ℂ d ρ ρ' (isSSRep_of_finite ρ)
    (isSSRep_of_finite ρ') (fun g => by
      show _ = Matrix.trace ((ρ (φ s g) : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      rw [← hρ, ← hρ, hYs])
  have hA' : ∀ g, ρ (φ s g) = A * ρ g * A⁻¹ := fun g => hA g
  have hAk : ∀ k : ℕ, ∀ g, ρ (((φ s) ^ k) g) = A ^ k * ρ g * (A ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', MulAut.mul_apply, hA', ih]; group
  set l := orderOf s with hl_def
  have hl : 0 < l := orderOf_pos s
  have hφl : (φ s) ^ l = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hB : ∀ g, A ^ l * ρ g = ρ g * A ^ l := by
    intro g
    have := hAk l g
    rw [hφl, MulAut.one_apply] at this
    calc A ^ l * ρ g = (A ^ l * ρ g * (A ^ l)⁻¹) * A ^ l := by group
      _ = ρ g * A ^ l := by rw [← this]
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_poly_pow_mul_eq_one' d l ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) hl (Units.isUnit _)
  set Bm : Matrix (Fin d) (Fin d) ℂ := ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) with hBm
  set C : Matrix (Fin d) (Fin d) ℂ := aeval Bm p with hC
  have hCA : Commute ((A : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    apply commute_aeval
    rw [hBm, Units.val_pow_eq_pow_val]
    exact (Commute.refl _).pow_right l
  have hCρ : ∀ g, Commute ((ρ g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    intro g
    apply commute_aeval
    have := congrArg (fun x : GL (Fin d) ℂ => (x : Matrix (Fin d) (Fin d) ℂ)) (hB g)
    simp only [Units.val_mul] at this
    exact this.symm
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl
  have h1 : C * (C ^ (l - 1) * Bm) = 1 := by
    rw [← mul_assoc, ← pow_succ', hl1]; exact hp
  let Cu : GL (Fin d) ℂ := ⟨C, C ^ (l - 1) * Bm, h1, mul_eq_one_comm.mp h1⟩
  have hCuA : A * Cu = Cu * A := Units.ext (hCA.eq)
  have hCuρ : ∀ g, Cu * ρ g = ρ g * Cu := fun g => Units.ext ((hCρ g).eq.symm)
  have hCuB : Cu ^ l * A ^ l = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]; exact hp)
  set A' : GL (Fin d) ℂ := A * Cu with hA'def
  have hA'l : A' ^ l = 1 := by
    rw [hA'def, (show Commute A Cu from hCuA).mul_pow, ((show Commute A Cu from hCuA).pow_pow l l).eq]
    exact hCuB
  have hA's : ∀ g, ρ (φ s g) = A' * ρ g * A'⁻¹ := by
    intro g
    rw [hA', hA'def, mul_inv_rev]
    calc A * ρ g * A⁻¹ = A * (ρ g * Cu) * Cu⁻¹ * A⁻¹ := by group
      _ = A * Cu * ρ g * (Cu⁻¹ * A⁻¹) := by rw [← hCuρ g]; group
  let σ : Γ →* GL (Fin d) ℂ := monoidHomOfForallMemZpowers hs (orderOf_dvd_of_pow_eq_one hA'l)
  have hσs : σ s = A' := monoidHomOfForallMemZpowers_apply_gen hs _
  let H : Subgroup Γ :=
    { carrier := {t | ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹}
      mul_mem' := by
        intro a b ha hb g
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, MulAut.mul_apply, ha, hb, map_mul]; group
      one_mem' := by intro g; simp
      inv_mem' := by
        intro a ha g
        simp only [Set.mem_setOf_eq] at *
        have := ha ((φ a⁻¹) g)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
        rw [map_inv σ]
        calc ρ (φ a⁻¹ g) = (σ a)⁻¹ * (σ a * ρ (φ a⁻¹ g) * (σ a)⁻¹) * σ a := by group
          _ = (σ a)⁻¹ * ρ g * ((σ a)⁻¹)⁻¹ := by rw [← this]; group }
  have hsH : s ∈ H := fun g => by rw [hσs]; exact hA's g
  have hall : ∀ t, ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹ := fun t => (Subgroup.zpowers_le.mpr hsH) (hs t)
  let Λ : G ⋊[φ] Γ →* GL (Fin d) ℂ := SemidirectProduct.lift ρ σ (fun t => by
    ext g : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hall t g)
  refine ⟨fun x => Matrix.trace ((Λ x : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ), ?_, ?_⟩
  · exact (GlobalTheory.BI.matrixChar_iff_isChar _ _).mp ⟨d, Λ, fun x => rfl⟩
  · intro g
    simp only [Λ, SemidirectProduct.lift_inl]
    exact (hρ g).symm

end GlobalTheory.StableExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionIntoInjectiveSheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NatFamExt

variable {R : Type} [CommRing R] (P : PSh)

def finMap {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) :
    (P.obj V →₀ F.obj V) →ₗ[ULift.{1} R] (P.obj W →₀ F.obj W) :=
  Finsupp.lmapDomain (F.obj W) (ULift.{1} R) (P.map g) ∘ₗ Finsupp.mapRange.linearMap (F.map g).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] (P : _root_.GlobalTheory.EtC.PSh) in
theorem _root_.GlobalTheory.NatFamExt.finMap_single {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : P.obj V) (a : F.obj V) :
    _root_.GlobalTheory.NatFamExt.finMap P g (Finsupp.single x a) =
      Finsupp.single (P.map g x) ((F.map g).hom a) := by
  simp [_root_.GlobalTheory.NatFamExt.finMap, Finsupp.mapDomain_single]

def finP (F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ (P.obj V →₀ F.obj V)
  map g := ModuleCat.ofHom (finMap P g)
  map_id V := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change finMap P (𝟙 V) (Finsupp.single x a) = Finsupp.single x a
    rw [finMap_single]
    simp
  map_comp f g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change finMap P (f ≫ g) (Finsupp.single x a) = finMap P g (finMap P f (Finsupp.single x a))
    rw [finMap_single, finMap_single, finMap_single]
    simp

def finPMap {F F' : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ F') : finP P F ⟶ finP P F' where
  app V := ModuleCat.ofHom (Finsupp.mapRange.linearMap (φ.app V).hom)
  naturality V W g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change Finsupp.mapRange.linearMap (φ.app W).hom (finMap P g (Finsupp.single x a)) =
      finMap P g (Finsupp.mapRange.linearMap (φ.app V).hom (Finsupp.single x a))
    rw [finMap_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, finMap_single]
    exact congrArg _ (congrArg (fun h => h.hom a) (φ.naturality g))

def famHom (G : Shv R) {A : Shv R} (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V)
    (hψ : ∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V),
      Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) :
    finP P A.obj ⟶ G.obj where
  app V := ModuleCat.ofHom (Finsupp.lsum (ULift.{1} R) (ψ V.unop))
  naturality V W g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change Finsupp.lsum (ULift.{1} R) (ψ W.unop) (finMap P g (Finsupp.single x a)) =
      (G.obj.map g).hom (Finsupp.lsum (ULift.{1} R) (ψ V.unop) (Finsupp.single x a))
    rw [finMap_single, Finsupp.lsum_single, Finsupp.lsum_single]
    exact (hψ _ _ g.unop x a).symm

end GlobalTheory.NatFamExt

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.natFam_extend_of_injective : ∀ (R : Type) [CommRing R] (P : _root_.GlobalTheory.EtC.PSh)
    (G : _root_.GlobalTheory.EtC.Shv R), Injective G → ∀ {A B : _root_.GlobalTheory.EtC.Shv R} (f : A ⟶ B), Mono f →
    ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) →
      _root_.GlobalTheory.EtC.Sec A V →ₗ[ULift.{1} R] _root_.GlobalTheory.EtC.Sec G V),
    (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : _root_.GlobalTheory.EtC.Sec A V),
      _root_.GlobalTheory.EtC.Sec.res w (ψ V x a) = ψ W (P.map w.op x) (_root_.GlobalTheory.EtC.Sec.res w a)) →
    ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) →
      _root_.GlobalTheory.EtC.Sec B V →ₗ[ULift.{1} R] _root_.GlobalTheory.EtC.Sec G V,
      (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : _root_.GlobalTheory.EtC.Sec B V),
        _root_.GlobalTheory.EtC.Sec.res w (χ V x b) = χ W (P.map w.op x) (_root_.GlobalTheory.EtC.Sec.res w b)) ∧
      ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : _root_.GlobalTheory.EtC.Sec A V),
        χ V x (_root_.GlobalTheory.EtC.Sec.map f a) = ψ V x a := by
  intro R _ P G hG A B f hf ψ hψ
  have hfval : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have hinj : ∀ V, Function.Injective (f.hom.app V).hom := fun V =>
    (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f.hom).1 hfval V)
  haveI : Injective G.obj :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology _) G
  haveI : Mono (_root_.GlobalTheory.NatFamExt.finPMap P f.hom) := by
    rw [NatTrans.mono_iff_mono_app]
    intro V
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) (hinj V)
  obtain ⟨θ, hθ⟩ := Injective.factors (_root_.GlobalTheory.NatFamExt.famHom P G ψ hψ)
    (_root_.GlobalTheory.NatFamExt.finPMap P f.hom)
  refine ⟨fun V x => (θ.app (op V)).hom ∘ₗ Finsupp.lsingle x, ?_, ?_⟩
  · intro V W w x b
    have h := congrArg (fun h => h.hom (Finsupp.single x b)) (θ.naturality w.op)
    change (θ.app (op W)).hom (_root_.GlobalTheory.NatFamExt.finMap P w.op (Finsupp.single x b)) =
      (G.obj.map w.op).hom ((θ.app (op V)).hom (Finsupp.single x b)) at h
    rw [_root_.GlobalTheory.NatFamExt.finMap_single] at h
    exact h.symm
  · intro V x a
    have h := congrArg (fun h => (h.app (op V)).hom (Finsupp.single x a)) hθ
    change (θ.app (op V)).hom
        (Finsupp.mapRange.linearMap (f.hom.app (op V)).hom (Finsupp.single x a)) =
      Finsupp.lsum (ULift.{1} R) (ψ V) (Finsupp.single x a) at h
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.lsum_single] at h
    exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfFibres
section
noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.CMVal.Fibre

variable {E : Type} [Field E] [NumberField E]


open Classical in
theorem tendsto_of_cut (a : Af E) (g : Finset (HeightOneSpectrum (𝓞 E)) → Af E)
    (hg : ∀ T v, g T v = if v ∈ T then a v else 1) : Tendsto g atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 E)) := {v | a v ∈ v.adicCompletionIntegers E}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 E)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  have h2 := ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf
  have h3 : g = (RestrictedProduct.inclusion _ _ hle) ∘ f :=
    funext fun T => Subtype.ext (funext fun v => hg T v)
  rw [h3]
  exact h2


open Classical in
theorem prod_single_apply (y : (Af E)ˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = if v ∈ T then (y : Af E) v else 1 := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, if_neg (Finset.notMem_empty v)]; rfl
  | insert u T hu ih =>
    rw [Finset.prod_insert hu, Units.val_mul]
    change (single u (coord u y) : Af E) v * ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = _
    rw [ih]
    by_cases h : v = u
    · subst h
      rw [single_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one, coe_coord]
    · rw [suppAt_single u _ v h, one_mul]; simp [h]

theorem coord_inv' (P : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : coord P y⁻¹ = (coord P y)⁻¹ := Units.ext rfl

theorem hasProd_single (y : (Af E)ˣ) : HasProd (fun P => single P (coord P y)) y := by
  have h : ∀ y : (Af E)ˣ, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) =>
      ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E)) atTop (𝓝 (y : Af E)) := fun y =>
    tendsto_of_cut _ _ (prod_single_apply y)
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, single P (coord P y)) atTop (𝓝 y)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h y).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h y⁻¹
  simp only [coord_inv', map_inv, Finset.prod_inv_distrib] at h2
  exact h2

theorem continuous_finPart (χ : HChar E) : Continuous (finPart χ) :=
  χ.2.1.comp (Continuous.units_map (MonoidHom.inr (InfiniteAdeleRing E) (Af E)) (continuous_const.prodMk continuous_id))

theorem hasProd_loc (χ : HChar E) (y : (Af E)ˣ) : HasProd (fun P => χ.loc P (coord P y)) (finPart χ y) :=
  (hasProd_single y).map (finPart χ) (continuous_finPart χ)

theorem finPart_eq_one_of_fibres (E : Type) [Field E] [NumberField E] (χ : HChar E) (y : (Af E)ˣ)
    (h : ∀ v : HeightOneSpectrum (OF E),
      ∏ P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, χ.loc P (coord P y) = 1) : finPart χ y = 1 := by
  classical
  let U : Finset (HeightOneSpectrum (OF E)) → Finset (HeightOneSpectrum (𝓞 E)) :=
    fun S => S.biUnion (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E))
  have hmem : ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)),
      P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := fun v P => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]; rfl
  have hU : Tendsto U atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun S S' hS => Finset.biUnion_subset_biUnion_of_subset_left _ hS) fun P => ?_
    exact ⟨{P.under (OF E)}, Finset.mem_biUnion.2 ⟨_, Finset.mem_singleton_self _, (hmem _ _).2 rfl⟩⟩
  have h1 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) atTop (𝓝 (finPart χ y)) :=
    hasProd_loc χ y
  have h2 := h1.comp hU
  have h3 : ((fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) ∘ U) = fun _ => 1 := by
    funext S
    change ∏ P ∈ S.biUnion _, _ = 1
    rw [Finset.prod_biUnion]
    · exact Finset.prod_eq_one fun v _ => h v
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (hmem _ _).1 hv, ← (hmem _ _).1 hw]
  rw [h3] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

end GlobalTheory.CMVal.Fibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModule
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem homSh_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M] :
    Injective ((homSh J).obj (op M)) := by
  obtain ⟨e, -, hX⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  haveI : Module.Projective (ULift.{1} R) M := (IsProjective.iff_projective (P := M)).2 ‹_›
  constructor
  intro X Y g i _
  have surj : Function.Surjective (Linear.leftComp (ULift.{1} R) J i) :=
    fun k => ⟨Injective.factorThru k i, Injective.comp_factorThru k i⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property _ (e X M g) surj
  refine ⟨(e Y M).symm h', ?_⟩
  apply (e X M).injective
  rw [hX, Equiv.apply_symm_apply, hh']

end GlobalTheory.EtC
end

