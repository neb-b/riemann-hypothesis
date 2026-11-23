module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocycleFormEqConnectionForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.ConnCocycle

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem divPowerCompatDeRhamRelIdeal_zero_dividedPowers (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : rel R (dp0 B) = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨n, a, ha, rfl⟩
  rw [Ideal.mem_bot.1 ha]
  simp [dpow_eval_zero]

theorem cocyc {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (k : (KK (dp0 R) s).Z1)
    {T T' : Thick (dp0 R) s} (φ : T ⟶ T') :
    k.1.2 T' = km1 (SemiHom.of_algHom φ.φ) φ.dp (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ) := by
  have h := congrArg (fun c ↦ c.2.1 T T' φ) (AddMonoidHom.mem_ker.1 k.2)
  change k.1.2 T' - _ - _ = 0 at h
  rw [sub_sub, sub_eq_zero] at h
  exact h

section
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def sndK : (diagExt R B).C →+ K1 R (dp0 B) :=
  AddMonoidHom.mk' (fun c ↦ Submodule.Quotient.mk (TrivSqZeroExt.snd c)) fun a b ↦ by
    rw [TrivSqZeroExt.snd_add, Submodule.Quotient.mk_add]

theorem sndK_apply (c : (diagExt R B).C) : sndK R B c = Submodule.Quotient.mk (TrivSqZeroExt.snd c) := rfl

theorem sndK_mul (x y : (diagExt R B).C) :
    sndK R B (x * y) = (diagExt R B).π x • sndK R B y + (diagExt R B).π y • sndK R B x := by
  show Submodule.Quotient.mk (x * y).snd = x.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) y.snd +
    y.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) x.snd
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1

theorem sndK_alg (r : R) : sndK R B (algebraMap R (diagExt R B).C r) = 0 := by
  rw [sndK_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, Submodule.Quotient.mk_zero]

theorem sndK_dpow (n : ℕ) (a : (diagExt R B).C) (ha : a ∈ RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) :
    sndK R B ((divided₂ (diagExt R B).sq).dpow (n + 1) a) =
      (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow n a) • sndK R B a := by
  rcases n with _ | m
  · rw [(divided₂ (diagExt R B).sq).dpow_one ha, (divided₂ (diagExt R B).sq).dpow_zero ha, map_one, one_smul]
  · have h0 : (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow (m + 1) a) = 0 :=
      (divided₂ (diagExt R B).sq).dpow_mem (Nat.succ_ne_zero m) ha
    rw [squareZeroDividedPowers_dpow _ (by omega), map_zero, h0, zero_smul]

end

section
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem deRhamAlgebraMap_sends_sectionOneForm (ρ : DR R (diagExt R B).C →+ DR R B) (hmul : ∀ x y, ρ (x * y) = ρ x * ρ y)
    (halg : ∀ c, ρ (algebraMap _ (DR R (diagExt R B).C) c) = algebraMap B (DR R B) ((diagExt R B).π c))
    (hD : ∀ c, ρ (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c))
    (α : B →ₐ[R] (diagExt R B).C) (hα : ∀ b, (diagExt R B).π (α b) = b)
    (g : Ω[B⁄R] →+ Ω[B⁄R]) (hg : ∀ b c : B, g (b • D R B c) = b • TrivSqZeroExt.snd (α c))
    (κ : Ω[B⁄R]) : ρ (ι1 ((SemiHom.of_algHom α).m1 κ)) = ι1 (g κ) := by
  induction κ using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, Algebra.smul_def, hmul, halg, hD, hg, map_smul,
      Algebra.smul_def]
    congr 2
    exact hα b
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end

theorem form_eq_connForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1)
    (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)),
    k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  intro R _ X s k f hk B _ _ x hx
  obtain ⟨ρ, hadd, hmul, halg, hD, hrel, -, -⟩ := GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R B ⊥ (dp0 B) (diagExt R B).C
    (RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) (divided₂ (diagExt R B).sq) (diagExt R B).π
    (sndK R B) (sndK_mul R B) (sndK_alg R B) (sndK_dpow R B)
  have h0 := divPowerCompatDeRhamRelIdeal_zero_dividedPowers R B
  simp only [h0, Ideal.mem_bot, sub_sub, sub_eq_zero] at hadd hmul halg hD hrel
  let ρh : DR R (diagExt R B).C →+ DR R B := AddMonoidHom.mk' ρ hadd
  have hD' : ∀ c, ρh (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c) := fun c ↦ hD c _ rfl
  let a := (diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl
  let a' := (diagExt R B).secHom hx (diagSec R B) (fst_derSec _)
  have c1 := cocyc k a
  have c2 := cocyc k a'
  rw [hk] at c1 c2
  obtain ⟨κ, hκ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 (Thick.triv B x hx))
  obtain ⟨θ, hθ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 ((diagExt R B).thick x hx))
  rw [← hκ, ← hθ, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at c1 c2
  have e1 : ρh (ι1 (θ - ((SemiHom.of_algHom a.φ).m1 κ + D R _ (f.1 _ _ a)))) = 0 := hrel _ c1
  have e2 : ρh (ι1 (θ - ((SemiHom.of_algHom a'.φ).m1 κ + D R _ (f.1 _ _ a')))) = 0 := hrel _ c2
  have r1 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a.φ (fun _ ↦ rfl) 0 (fun b c ↦ by
    show (0 : Ω[B⁄R]) = b • TrivSqZeroExt.snd (TrivSqZeroExt.inl c : TrivSqZeroExt B Ω[B⁄R])
    rw [TrivSqZeroExt.snd_inl, smul_zero])
  have r2 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a'.φ (fst_derSec _) (AddMonoidHom.id _) (fun b c ↦ by
    show b • D R B c = b • TrivSqZeroExt.snd (diagSec R B c)
    rw [snd_derSec])
  simp only [map_sub, map_add (f := _), r1, r2, hD', AddMonoidHom.zero_apply, AddMonoidHom.id_apply, map_zero,
    zero_add] at e1 e2
  rw [← hκ, Submodule.Quotient.eq]
  change ι1 _ ∈ rel R (dp0 B)
  rw [h0, Ideal.mem_bot, map_sub, sub_eq_zero]
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  change ι1 κ = ι1 (TrivSqZeroExt.snd (f.1 _ _ a)) - ι1 (TrivSqZeroExt.snd (f.1 _ _ a'))
  linear_combination (norm := abel1) e1 - e2

end GlobalTheory.ConnCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.InvAlg

theorem ker_evalₐ {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval J.fg_of_isNoetherianRing, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

theorem completion_invariants_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  intro R _ _ _ hR R' _ _ _ _ hinj hgal C' _ _ _ _ _ act hact O _ _ _ _ i h1 h2 h3 C hC hCft hCfin e
  classical
  haveI : IsNoetherianRing R := hR.1
  haveI := hCft
  haveI := hCfin
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  haveI : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing R O
  haveI : Finite (Gal (algebraMap R R')) := hgal.1
  let T := TensorProduct R O R'
  let JC : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let JO : Ideal O := (maximalIdeal R).map (algebraMap R O)
  let IC : Ideal C' := JC.map (algebraMap C C')
  let IT : Ideal T := JO.map (algebraMap O T)
  let gC : Gal (algebraMap R R') → (C' →ₐ[C] C') := fun σ =>
    { (act σ).toRingEquiv.toRingHom with commutes' := fun c => (hC _).1 c.2 σ }

  have hfixC : ∀ x : C', x ∈ LinearMap.range (Algebra.linearMap C C') ↔ ∀ σ, (gC σ).toLinearMap x = x := by
    intro x; constructor
    · rintro ⟨c, rfl⟩ σ; exact (gC σ).commutes c
    · intro hx; exact ⟨⟨x, (hC x).2 hx⟩, rfl⟩
  have hmC := _root_.GlobalTheory.adicCompletion_map_invariants C JC C C' (Algebra.linearMap C C') _ (fun σ => (gC σ).toLinearMap) Subtype.val_injective hfixC
  obtain ⟨injC, rangeC⟩ := _root_.GlobalTheory.InvAlg.cmap_transfer C C' JC _ gC hmC.1 hmC.2

  obtain ⟨injOT, fixOT⟩ := _root_.GlobalTheory.InvAlg.flat_tensor_invariants R R' O hinj hgal
  have hfixO : ∀ t : T, t ∈ LinearMap.range (Algebra.linearMap O T) ↔
      ∀ σ, (galTensor O σ).toLinearMap t = t := by
    intro t; constructor
    · rintro ⟨x, rfl⟩ σ; exact (galTensor O σ).commutes x
    · intro ht; obtain ⟨x, hx⟩ := fixOT t ht; exact ⟨x, hx⟩
  have hmO := _root_.GlobalTheory.adicCompletion_map_invariants O JO O T (Algebra.linearMap O T) _ (fun σ => (galTensor O σ).toLinearMap) injOT hfixO
  obtain ⟨injO, rangeO⟩ := _root_.GlobalTheory.InvAlg.cmap_transfer O T JO _ (galTensor O) hmO.1 hmO.2

  have hIT : IT = (maximalIdeal R).map (algebraMap R T) := by
    simp only [IT, JO, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hIC : IC = (maximalIdeal R).map (algebraMap R C') := by
    simp only [IC, JC, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hCσ : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC := fun σ => map_algebraMap_le (gC σ) JC
  obtain ⟨Ψ, hΨσ, hΨi⟩ := _root_.GlobalTheory.InvAlg.Levels.levels_equiv R (maximalIdeal R) R' C' act hact O i h1 h2 h3 IT IC hIT hIC
    (fun σ => map_algebraMap_le (galTensor O σ) JO) hCσ
  let κC := cmap (algebraMap C C') JC IC le_rfl
  let κO1 := cmap (algebraMap O T) JO IT le_rfl
  let κO : AdicCompletion JO O →+* AdicCompletion IC C' := (Ψ : _ →+* _).comp κO1
  have hr : ∀ y, y ∈ Set.range κO ↔ y ∈ Set.range κC := by
    intro y
    rw [rangeC y]
    have : y ∈ Set.range κO ↔ Ψ.symm y ∈ Set.range κO1 := by
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by simp [κO]⟩
      · rintro ⟨a, ha⟩; exact ⟨a, by simp [κO, ha]⟩
    rw [this, rangeO]
    refine forall_congr' fun σ => ?_
    rw [← Ψ.injective.eq_iff, hΨσ, Ψ.apply_symm_apply]
  have hrange : κO.range = κC.range := by ext y; exact hr y
  have injκO : Function.Injective κO := Ψ.injective.comp injO
  let eO : AdicCompletion JO O ≃+* κO.range := RingEquiv.ofBijective κO.rangeRestrict
    ⟨fun a b h => injκO (congrArg Subtype.val h), κO.rangeRestrict_surjective⟩
  let eC : AdicCompletion JC C ≃+* κC.range := RingEquiv.ofBijective κC.rangeRestrict
    ⟨fun a b h => injC (congrArg Subtype.val h), κC.rangeRestrict_surjective⟩
  let Θ : AdicCompletion JO O ≃+* AdicCompletion JC C := (eO.trans (RingEquiv.subringCongr hrange)).trans eC.symm
  have hΘ : ∀ a, κC (Θ a) = κO a := fun a =>
    congrArg Subtype.val (eC.apply_symm_apply ((RingEquiv.subringCongr hrange) (eO a)))

  have hΘR : ∀ r : R, Θ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    apply injC
    rw [hΘ]
    show Ψ (κO1 (algebraMap R (AdicCompletion JO O) r)) = κC (algebraMap R (AdicCompletion JC C) r)
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, cmap_of, cmap_of,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← AdicCompletion.algebraMap_apply IT r, ← AdicCompletion.algebraMap_apply IC r]
    exact Ψ.commutes r
  have hOm : ∀ k, (JO ^ k).map (algebraMap O (AdicCompletion JO O)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JO O)) := by
    intro k; simp only [JO, Ideal.map_pow, Ideal.map_map]; rfl
  have hCm : ∀ k, (JC ^ k).map (algebraMap C (AdicCompletion JC C)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JC C)) := by
    intro k; simp only [JC, Ideal.map_pow, Ideal.map_map]; rfl
  have key : ∀ a, AdicCompletion.evalₐ JC (e + 1) (Θ a) = 0 ↔ AdicCompletion.evalₐ JO (e + 1) a = 0 := by
    intro a
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, ker_evalₐ, ker_evalₐ, hOm, hCm]
    have hmap : ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JC C))) =
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JO O))).map (Θ : _ →+* _) := by
      rw [Ideal.map_map]; congr 1; exact RingHom.ext fun r => (hΘR r).symm
    rw [hmap, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
  have hJC : JC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C) := (Ideal.map_pow _ _ _).symm
  let ψ0 : O →+* C ⧸ JC ^ (e + 1) :=
    (AdicCompletion.evalₐ JC (e + 1) : AdicCompletion JC C →+* C ⧸ JC ^ (e + 1)).comp
      ((Θ : _ →+* _).comp (algebraMap O (AdicCompletion JO O)))
  have hψ0 : ∀ x, ψ0 x = AdicCompletion.evalₐ JC (e + 1) (Θ (AdicCompletion.of JO O x)) := fun x => rfl
  have hsurj : Function.Surjective ψ0 := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ JO (e + 1) (Θ.symm (AdicCompletion.of JC C c)))
    refine ⟨x, ?_⟩
    have h0 : AdicCompletion.evalₐ JO (e + 1)
        (AdicCompletion.of JO O x - Θ.symm (AdicCompletion.of JC C c)) = 0 := by
      rw [map_sub, AdicCompletion.evalₐ_of, hx, sub_self]
    have h1 := (key _).2 h0
    rw [map_sub, map_sub, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_of, sub_eq_zero] at h1
    rw [hψ0, h1]
  have hker : RingHom.ker ψ0 = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O) := by
    ext x
    rw [RingHom.mem_ker, hψ0, key, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    simp only [JO, Ideal.map_pow]
  let gR : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃+*
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).trans
      (Ideal.quotEquivOfEq hJC)
  have hgR : ∀ x, gR (Ideal.Quotient.mk _ x) = Ideal.quotEquivOfEq hJC (ψ0 x) := fun x => rfl
  let gm : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R]
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    AlgEquiv.ofRingEquiv (f := gR) (fun r => by
      change gR (Ideal.Quotient.mk _ (algebraMap R O r)) = Ideal.Quotient.mk _ (algebraMap R C r)
      rw [hgR, hψ0, ← AdicCompletion.algebraMap_apply JO r, hΘR, AdicCompletion.algebraMap_apply,
        AdicCompletion.evalₐ_of, Ideal.quotEquivOfEq_mk])
  refine ⟨gm, fun x c hxc => ?_⟩
  have h1' : ψ0 x = Ideal.Quotient.mk (JC ^ (e + 1)) c := by
    apply (Ideal.quotEquivOfEq hJC).injective
    rw [Ideal.quotEquivOfEq_mk]; exact (hgR x).symm.trans hxc
  have h2' : AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R')))) =
      Ideal.Quotient.mk (IC ^ (e + 1)) (c : C') := by
    have := congrArg (Ideal.quotientMap (IC ^ (e + 1)) (algebraMap C C')
      (pow_le_comap (algebraMap C C') (le_rfl : JC.map (algebraMap C C') ≤ IC) (e + 1))) h1'
    rw [hψ0, ← evalₐ_cmap] at this
    change AdicCompletion.evalₐ IC (e + 1) (κC (Θ _)) = _ at this
    rw [hΘ] at this
    rw [show κO (AdicCompletion.of JO O x) = Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R'))) from by
      show Ψ (κO1 _) = _
      rw [cmap_of]; rfl] at this
    rw [this, Ideal.quotientMap_mk]; rfl
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i e x)
  have h3' := hΨi e x y hy
  rw [h2', Ideal.Quotient.eq] at h3'
  rw [← hy, Ideal.Quotient.eq]
  have hpow : IC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C') := by rw [hIC, Ideal.map_pow]
  rw [← hpow]; exact h3'

end GlobalTheory.InvAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecomposition
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecC

theorem frame_power_identity : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L M : LB A.left) (g : ℕ) (uL : HolUnif A L g) (uM : HolUnif A M g)
    (HL HM : Matrix (Fin g) (Fin g) ℂ) (χL : uL.Λ → ℂ) (χM : uM.Λ → ℂ), uM.ex = uL.ex →
    GlobalTheory.TorusRM.IsFactorAH uL HL χL → GlobalTheory.TorusRM.IsFactorAH uM HM χM →
    (∀ l, χL l = 1 ∨ χL l = -1) → (∀ l, χM l = 1 ∨ χM l = -1) →
    ∀ (N : ℕ) (K : Type) [Fintype K] (F : K → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ), Even N → (∀ k, Even (ε k)) →
    (∀ k, ∀ l ∈ uL.Λ, F k l ∈ uM.Λ) →
    (∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ HL.mulVec (star w)) = ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k w)))) →
    ∀ (l : uL.Λ) (i : L.ι) (j : K → M.ι) (z : Fin g → ℂ), ⊤ ≤ (uL.ex z).left ⁻¹ᵁ L.U i →
      (∀ k, ⊤ ≤ (uM.ex (F k z)).left ⁻¹ᵁ M.U (j k)) →
      uL.fr i z ^ N * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k = uL.fr i (z + l) ^ N * ∏ k, uM.fr (j k) (F k z) ^ ε k := by
  intro A _ L M g uL uM HL HM χL χM _ hfL hfM hχL hχM N K _ F ε hN hε hF hdec l i j z hi hj
  have hL1 := hfL.2.2 l i z hi
  have hM1 : ∀ k, uM.fr (j k) (F k z) = χM ⟨F k l, hF k l l.2⟩ *
      Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) * uM.fr (j k) (F k (z + l)) := fun k => by
    rw [map_add (f := _)]
    exact hfM.2.2 ⟨F k l, hF k l l.2⟩ (j k) (F k z) (hj k)
  have hcL : χL l ^ N = 1 := by
    rcases hχL l with h | h <;> rw [h]
    · exact one_pow N
    · exact hN.neg_one_pow
  have hcM : ∀ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k = 1 := fun k => by
    rcases hχM ⟨F k l, hF k l l.2⟩ with h | h <;> rw [h]
    · exact one_zpow _
    · exact (hε k).neg_one_zpow
  have hR : ∏ k, uM.fr (j k) (F k z) ^ ε k = (∏ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k) *
      (∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k) * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hM1 k, mul_zpow, mul_zpow]
  have key : Complex.exp (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) ^ N =
      ∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k := by
    rw [← Complex.exp_nat_mul, Finset.prod_congr rfl (fun k _ => (Complex.exp_int_mul _ (ε k)).symm),
      ← Complex.exp_sum]
    congr 1
    have h1 := hdec z l
    have h2 := hdec l l
    calc (N : ℂ) * (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))))
        = Real.pi * ((N : ℂ) * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) +
          Real.pi / 2 * ((N : ℂ) * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) := by ring
      _ = Real.pi * ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
          Real.pi / 2 * ∑ k, (ε k : ℂ) * (F k l ⬝ᵥ HM.mulVec (star (F k l))) := by rw [h1, h2]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
  rw [hR, hL1, mul_pow, mul_pow, hcL, Finset.prod_eq_one (fun k _ => hcM k), key]
  ring

theorem lbIso_of_sameFactor (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (X Y : LB A.left) (g : ℕ)
    (u : HolUnif A X g) (v : HolUnif A Y g) (hX : X.IsLB) (hY : Y.IsLB) (hex : v.ex = u.ex)
    (hper : ∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ X.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ Y.U j →
      u.fr i z * v.fr j (z + l) = u.fr i (z + l) * v.fr j z) : LBIso X Y := by
  haveI := hA.comm
  haveI := hA.smooth
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := HolUnifSec.exists_isFn (SameFactor.divUnif u v hex) hA hp (LB.isLB_div hY hX)
    (θ := fun _ => 1) (differentiable_const _) (by
      intro l hl p z hz
      obtain ⟨hz1, hz2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e := hper ⟨l, hl⟩ p.2 p.1 z hz2 hz1
      have hl' : u.ex (z + l) = u.ex z := by
        rw [u.ex_add, (u.ker _).2 hl, _root_.mul_one]
      have n1 := u.fr_ne p.2 z hz2
      have n2 := u.fr_ne p.2 (z + l) (by rw [hl']; exact hz2)
      change 1 * (v.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (v.fr p.1 z * (u.fr p.2 z)⁻¹)
      field_simp
      linear_combination e)
  exact SameFactor.exists_gen_of_isFn _ s _ hs fun _ => one_ne_zero

theorem sqDec_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB →
    RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L →
    LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  intro A _ hA L M hL hM haL haM hsL hsM
  haveI := hA.comm
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim ℂ A hA
  obtain ⟨L₀, ⟨u₀⟩⟩ := HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨uL, HL, χL, hexL, hfL⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ L hL
  obtain ⟨uM, HM, χM, hexM, hfM⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  have hposL := AmpleHermPos.re_form_pos_of_relAmple A hA L hL haL g uL HL χL hfL.1 hfL.2.1 hfL.2.2
  have hposM := AmpleHermPos.re_form_pos_of_relAmple A hA M hM haM g uM HM χM hfM.1 hfM.2.1 hfM.2.2
  have hAHL := TorusRM.isAH_of_isFactorAH hfL hposL
  have hAHM := TorusRM.isAH_of_isFactorAH hfM hposM
  have hex : uM.ex = uL.ex := hexM.trans hexL.symm
  have hΛ : ∀ z, z ∈ uM.Λ ↔ z ∈ uL.Λ := fun z => by rw [← uM.ker, ← uL.ker, hex]
  have hχL := ThetaUnifCompare.chi_eq_one_or_of_sym hL (sym_of_lbIso_neg hsL.symm) hAHL
  have hχM := ThetaUnifCompare.chi_eq_one_or_of_sym hM (sym_of_lbIso_neg hsM.symm) hAHM
  have hiL : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HL.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hL hAHL ⟨l, hl⟩ ⟨m, hm⟩
  have hiM : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HM.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hM hAHM ⟨l, (hΛ l).2 hl⟩ ⟨m, (hΛ m).2 hm⟩
  obtain ⟨N, a₀, r, a, F, hN, ha₀, hNe, ha₀e, hae, hF, hdec⟩ :=
    _root_.GlobalTheory.Desc.HermComb.main g uL.Λ uL.discrete uL.full HL HM hAHL.1 hAHM.1 hposL hposM hiL hiM
  choose β hβ hβF using fun i => _root_.GlobalTheory.UnifEndo.exists_isMonHom_of_map_lattice A hA L g uL (F i) (hF i)
  let f : Option (Fin r) → (A ⟶ A) := fun o => o.elim (𝟙 A) β
  let FF : Option (Fin r) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun o => o.elim LinearMap.id F
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  have hfF : ∀ k z, uM.ex (FF k z) = uL.ex z ≫ f k := by
    intro k z
    cases k with
    | none => simp [FF, f, hex]
    | some i => simpa [FF, f, hex] using hβF i z
  obtain ⟨u₁, hex₁, -, hfr₁⟩ := exists_holUnif_linComb A A L M g g uL uM _ f FF ε hfF
  have hcomb : LB.LinComb M (fun k => (f k).left) ε = LB.LinComb M (fun (o : Option (Fin r)) => o.elim (𝟙 A.left) fun i => (β i).left)
      (fun (o : Option (Fin r)) => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) := by
    congr 1
    funext o
    cases o <;> rfl
  refine ⟨N, a₀, r, a, β, hN, ha₀, hβ, ?_⟩
  rw [← hcomb]
  refine lbIso_of_sameFactor A hA _ _ g (ThetaGAGA.powFrame uL N) u₁ (isLB_lbPow hL N) (LB.isLB_linComb hM _ _)
    hex₁ ?_
  intro l i j z hi hj
  refine (congrArg₂ (· * ·) rfl (hfr₁ j (z + l))).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (hfr₁ j z)).symm)
  have hi' := ThetaGAGA.top_le_of_lbPow uL N i hi
  have hj' : ∀ k, ⊤ ≤ (uM.ex (FF k z)).left ⁻¹ᵁ M.U (j k) := fun k => by
    rw [hfF k z]
    exact (CubeValues.le_preimage_wchart (uL.ex z).left M (fun k => (f k).left) j).1 hj k
  exact frame_power_identity A L M g uL uM HL HM χL χM hex hfL hfM hχL hχM N _ FF ε hNe
    (fun k => by cases k with | none => exact (Int.even_coe_nat _).2 ha₀e | some i => exact (Int.even_coe_nat _).2 (hae i))
    (fun k l hl => by cases k with | none => exact (hΛ l).2 hl | some i => exact (hΛ _).2 (hF i l hl))
    (fun z w => by rw [Fintype.sum_option, hdec z w]; simp [FF, ε]) l (i PUnit.unit) j z hi' hj'

end GlobalTheory.SqDecC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMul
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem bas_repr_mul (n : ℕ) (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ T, ∑ U, (bas n).repr x T * (bas n).repr y U * (bas n).repr (bas n T * bas n U) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

theorem contDiff_coeff_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  intro n m F G
  refine ⟨fun s hF hG S => ?_, fun v hF hG S => ?_⟩
  · rw [show (fun v => (bas n).repr (F v * G v) S) = _ from funext fun v => bas_repr_mul n (F v) (G v) S]
    exact ContDiffOn.sum fun T _ => ContDiffOn.sum fun U _ => ((hF T).mul (hG U)).mul contDiffOn_const
  · rw [show (fun x => (bas n).repr (F x * G x) S) = _ from funext fun x => bas_repr_mul n (F x) (G x) S]
    exact DifferentiableAt.fun_sum fun T _ => DifferentiableAt.fun_sum fun U _ =>
      ((hF T).fun_mul (hG U)).fun_mul (differentiableAt_const _)

end GlobalTheory.CxForm
end

