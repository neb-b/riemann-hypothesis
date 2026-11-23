module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExpEmb
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

theorem expEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.Rg.BcB.N3.ExpEmb k := by
  intro n V _ _ π ξ hπ ⟨ℓ, hℓ0, hℓ⟩
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar fun i => unrChar k (ξ i)
  let ρ := (ofChar χ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨ℓ, fun g => LinearMap.ext fun v => by
      have h := hℓ ((leviTorus k (Fin n)).symm g) v
      have e : jacB π ((leviTorus k (Fin n)).symm g) = jac (points (Fin n)) π g := by
        show (jac (points (Fin n)) π) ((leviTorus k (Fin n)) ((leviTorus k (Fin n)).symm g)) = _
        rw [MulEquiv.apply_symm_apply]
      rw [e] at h
      refine h.trans ?_
      exact (ofChar_apply χ ((leviTorus k (Fin n)).symm g) (ℓ v)).symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hℓ0 ?_⟩
  have : φ = GlobalTheory.SmGL.Model.evalOne (points (Fin n)) (0 : π.IntertwiningMap (iP (k := k) ξ)) := by
    rw [← hf, h0]
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 := congrArg (fun F => F (Submodule.Quotient.mk v)) this
  exact h1

end PositivityTheory.Rg.BcB.N3.Pee
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GaloisFixedAdelicMatricesDescend
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem extremeSph_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hC : SphConst k) (hS : SphEmb k) (hU : UniqSub k) : ExtremeSph k := by
  intro h0 n ξ hm V _ _ π hs hi ⟨f, hf⟩
  obtain ⟨W, _, _, σ, hσs, hσi, hσsph, hσq⟩ := hC n ξ
  obtain ⟨g, hg⟩ := hS n ξ hm W σ hσs hσi hσsph hσq
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσsph
  have hg0 : g ≠ 0 := fun e => hw0 (hg (by rw [e, map_zero]; rfl))
  obtain ⟨e⟩ := hU h0 n ξ hm V W π σ hi hσi f g hf hg0
  refine fun hb => hw0 ?_
  have hv : e.toLinearEquiv.symm w ∈ fixed π (KO k (Fin n)) := fun h => by
    have h1 := hwK h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h2 := e.isIntertwining' h
    have h3 := congrArg (fun F => F (e.toLinearEquiv.symm w)) h2
    simp only [LinearMap.comp_apply] at h3
    refine (h3.trans ?_).trans h1
    show σ h (e.toLinearEquiv (e.toLinearEquiv.symm w)) = σ h w
    rw [LinearEquiv.apply_symm_apply]
  rw [hb] at hv
  have h5 := congrArg e.toLinearEquiv ((Submodule.mem_bot ℂ).1 hv)
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h5

theorem galois_fixed_adelic_matrices_descend (hE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExpEmb k)
    (hX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExtremeSph k)
    (hL : SatLink) : N3 := by
  intro E _ _ w c n N h σ P ξ hq he hm
  obtain ⟨f, hf⟩ := hE (w.adicCompletion E) n P.V P.ρ ξ P.smooth he
  have hc : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact hL E w c n N h σ P ξ hq (hX (w.adicCompletion E) hc n ξ hm P.V P.ρ P.smooth P.irred ⟨f, hf⟩) ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.Pee
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.InjectiveOfIrred
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LFun
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.N3.Psl

open PositivityTheory.Rg.BcB.N3

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro y
  have e : {g : G | S.toRepresentation g y = y} = {g : G | ρ g (y : V) = y} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [e]
  exact hρ (y : V)

theorem injective_of_irred {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hi : ρ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    Function.Injective f := by
  have := hi
  exact (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf

theorem coe_mem_fixed {ρ : Representation ℂ G V} (S : Subrepresentation ρ) {K : Subgroup G}
    {s : S.toSubmodule} (hs : s ∈ fixed S.toRepresentation K) : s.1 ∈ fixed ρ K :=
  GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hs g hg)

theorem hI {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (g : G) (y : V) : f (ρ g y) = σ g (f y) :=
  Representation.IntertwiningMap.isIntertwining _ _ f g y

set_option maxHeartbeats 4000000 in
theorem satLink : SatLink := by
  intro E _ _ w c n N h σ P ξ hq hsph ⟨f, hf⟩
  have hKO : ∀ m, KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hc : IsCompact (KO (w.adicCompletion E) (Fin n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isCompact_KO

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hfi := injective_of_irred P.irred f hf

  have hy : f x ∈ fixed (iP (k := w.adicCompletion E) ξ) (KO _ (Fin n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hI f, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
  have hy0 : f x ≠ 0 := fun e => hx0 (hfi (e.trans (map_zero f).symm))
  have hφ : Formalism.UG.IsSpherical E w (fun i => (ξ i : ℂ)) (f x).1.1 :=
    (SphCompletion.isSpherical_iff E w n ξ _).2 ⟨f x, hy, rfl⟩
  have hφ0 : (f x).1.1 ≠ 0 := fun e => hy0 (Subtype.ext (Subtype.ext e))
  have hsatφ := isSatVecGL_of_isSpherical (w := w) hφ hφ0
  have hsatY : IsSatVecGL w (iP (k := w.adicCompletion E) ξ) (f x) (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map (ρ' := rightReg ℂ _ ℂ) ((Submodule.subtype _).comp (Submodule.subtype _))
      (fun _ _ => rfl) (fun u v e => Subtype.ext (Subtype.ext e)) hsatφ
  have hsatX : IsSatVecGL w P.ρ x (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map f.toLinearMap (fun g y => hI f g y) hfi hsatY

  obtain ⟨S, q, hqs⟩ := hq
  obtain ⟨s0, hs0⟩ := hqs x
  have hSs : IsSmooth S.toRepresentation := isSmooth_sub (isSmooth_parInd _ _) S
  set s := GlobalTheory.LocGL.idem hSs hc s0 with hsdef
  have hqs' : q s = x := by
    rw [hsdef, GlobalTheory.LocGL.map_idem hSs P.smooth hc q s0, hs0, GlobalTheory.LocGL.idem_of_mem P.smooth hc hx]
  have hsfix : s ∈ fixed S.toRepresentation (KO _ (Fin n)) := GlobalTheory.LocGL.idem_mem hSs hc s0
  have htfix : s.1 ∈ fixed (locProd h w σ) (KGL w (n := n)) := by
    rw [hKO]
    exact coe_mem_fixed S hsfix
  have ht0 : s.1 ≠ 0 := fun e => hx0 (by rw [← hqs', show s = 0 from Subtype.ext e, map_zero])
  obtain ⟨B, hB, hsat⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (fun i => (σ i).smooth) (fun i => (σ i).irred) htfix ht0
  have hsatS : IsSatVecGL w S.toRepresentation s (∑ i, B i) :=
    IsSatVecGL.of_map (S.toSubmodule.subtype) (fun _ _ => rfl) Subtype.val_injective hsat
  have hsatX' : IsSatVecGL w P.ρ x (∑ i, B i) := by
    have := hsatS.map q.toLinearMap (fun g y => hI q g y) (by
      show q s ≠ 0
      rw [hqs']; exact hx0)
    rwa [show q.toLinearMap s = x from hqs'] at this
  exact ⟨fun i => (hB i).1, B, hB, hsatX'.unique hsatX⟩

end PositivityTheory.Rg.BcB.N3.Psl
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def KInj {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (T : π.IntertwiningMap σ) : Prop :=
  ∀ v ∈ fixed π (KO k (Fin n)), T v = 0 → v = 0

def GL2SphericalSwap : Prop := ∀ a b : ℂˣ, ‖(a : ℂ)‖ ≤ ‖(b : ℂ)‖ →
  ∃ T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a]), KInj k T

def StageLift : Prop := ∀ (n : ℕ) (η : Fin n → ℂˣ) (i j : Fin n), j.val = i.val + 1 →
  (∃ T : (iP (k := k) ![η i, η j]).IntertwiningMap (iP (k := k) ![η j, η i]), KInj k T) →
  ∃ T : (iP (k := k) η).IntertwiningMap (iP (k := k) (η ∘ Equiv.swap i j)), KInj k T

def ExpSph : Prop := ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
  IsSmooth π → π.IsIrreducible → IsSpherical π → ∃ (η : Fin n → ℂˣ) (f : π.IntertwiningMap (iP (k := k) η)), f ≠ 0

def SatPerm : Prop := ∀ (n : ℕ) (ξ η : Fin n → ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → IsSpherical π → IsSubquotient π (iP (k := k) ξ) →
  (∃ f : π.IntertwiningMap (iP (k := k) η), f ≠ 0) → ∃ σ : Equiv.Perm (Fin n), η = ξ ∘ σ

def Bubble : Prop := StageLift k → GL2SphericalSwap k → ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (σ : Equiv.Perm (Fin n)) (V : Type)
  [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), π.IsIrreducible → IsSpherical π →
  (∃ f : π.IntertwiningMap (iP (k := k) (ξ ∘ σ)), Function.Injective f) →
  ∃ f : π.IntertwiningMap (iP (k := k) ξ), Function.Injective f

end PositivityTheory.Rg.BcB.N3.Pse

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ValuationDetKO
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace PositivityTheory.Rg.BcB.N3.Pee

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_det_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨g', rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g') : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g' : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  exact h1.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

private theorem deltaHalf_and_torusChar_eq_one_of_mem_KO (n : ℕ) (ξ : Fin n → ℂˣ) (b : parab k (points (Fin n)))
    (hb : (b : GL (Fin n) k) ∈ KO k (Fin n)) :
    deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) b) = 1 ∧
    torusChar (fun i => unrChar k (ξ i)) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) b)) = 1 := by
  have hL := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.1 b hb
  have hp {α β ι : Type} [Monoid α] [CommMonoid β] (s : Finset ι)
      (f : ι → α →* β) (x : α) : (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih]
  constructor
  · rw [deltaHalf, hp]
    refine Finset.prod_eq_one (fun a _ => ?_)
    rw [MonoidHom.comp_apply, detChar_apply]
    exact isUnram_absPow k _ _ (valuation_det_KO (hL a))
  · rw [torusChar, hp]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have h0 : ord k (GeneralLinearGroup.det (leviProj k (points (Fin n)) b i)) = 0 :=
      ord_eq_zero_iff.mpr (valuation_det_KO (hL i))
    show (ξ i) ^ ord k (GeneralLinearGroup.det (leviProj k (points (Fin n)) b i)) = 1
    rw [h0, zpow_zero]

theorem exists_sph (n : ℕ) (ξ : Fin n → ℂˣ) :
    ∃ f : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (ξ i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom), f ∈ fixed (iP (k := k) ξ) (KO k (Fin n)) ∧ f ≠ 0 := by
  set μ : parab k (points (Fin n)) → ℂ := fun b =>
    ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) b) : ℂˣ) : ℂ) *
      ((torusChar (fun i => unrChar k (ξ i)) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) b)) : ℂˣ) : ℂ) with hμ
  have μmul : ∀ a b : parab k (points (Fin n)), μ (a * b) = μ a * μ b := by
    intro a b
    simp only [hμ, map_mul, Units.val_mul]
    ring
  have μone : ∀ b : parab k (points (Fin n)), (b : GL (Fin n) k) ∈ KO k (Fin n) → μ b = 1 := by
    intro b hb
    obtain ⟨h1, h2⟩ := deltaHalf_and_torusChar_eq_one_of_mem_KO n ξ b hb
    simp only [hμ, h1, h2, Units.val_one, mul_one]
  have hdec := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.2.2.2.2.2.2.2
  choose p hp x hx hg using hdec
  have wd : ∀ (q : parab k (points (Fin n))) (y : GL (Fin n) k), y ∈ KO k (Fin n) → ∀ g, g = (q : GL (Fin n) k) * y →
      μ ⟨p g, hp g⟩ = μ q := by
    intro q y hy g hgq
    have hmem : (q : GL (Fin n) k)⁻¹ * p g ∈ parab k (points (Fin n)) := mul_mem (inv_mem q.2) (hp g)
    have hK : (q : GL (Fin n) k)⁻¹ * p g ∈ KO k (Fin n) := by
      have : (q : GL (Fin n) k)⁻¹ * p g = y * (x g)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
        exact (hg g).symm.trans hgq
      rw [this]
      exact mul_mem hy (inv_mem (hx g))
    have e1 : (⟨p g, hp g⟩ : parab k (points (Fin n))) = q * ⟨_, hmem⟩ := by
      ext1
      simp
    rw [e1, μmul, μone ⟨_, hmem⟩ hK, mul_one]
  set φ : GL (Fin n) k → ℂ := fun g => μ ⟨p g, hp g⟩ with hφ
  have c1 : ∀ (b : borel k (Fin n)) (g : GL (Fin n) k), φ (b * g) =
      ↑((deltaHalf k fun (x : Fin n) ↦ Unit) ((leviProj k (points (Fin n))) b)) •
        ((MonoidHom.comp (ofChar (torusChar (fun i => unrChar k (ξ i)))) (leviTorus k (Fin n)).symm.toMonoidHom)
          ((leviProj k (points (Fin n))) b)) (φ g) := by
    intro b g
    have e2 : φ (b * g) = μ (⟨b.1, b.2⟩ * ⟨p g, hp g⟩) := by
      refine wd _ (x g) (hx g) _ ?_
      rw [Subgroup.coe_mul, mul_assoc, ← hg g]
    rw [e2, μmul]
    change _ = ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) ⟨b.1, b.2⟩) : ℂˣ) : ℂ) *
      (((torusChar (fun i => unrChar k (ξ i)) ((leviTorus k (Fin n)).symm
        (leviProj k (points (Fin n)) ⟨b.1, b.2⟩)) : ℂˣ) : ℂ) * φ g)
    simp only [hμ, hφ]
    ring
  have c2 : ∀ w ∈ KO k (Fin n), ∀ (g : GL (Fin n) k), φ (g * w) = φ g := by
    intro w hw g
    exact wd ⟨p g, hp g⟩ (x g * w) (mul_mem (hx g) hw) _ (by rw [← mul_assoc, ← hg g])
  obtain ⟨f, hf, hfφ⟩ := (SphCompletion.exists_fixed_iff (k := k) (fun i => unrChar k (ξ i)) φ).mpr ⟨c1, c2⟩
  refine ⟨f, hf, fun h0 => ?_⟩
  have h1 : φ 1 = 1 := by
    rw [hφ]
    simp only
    rw [wd 1 1 (one_mem _) 1 (by simp)]
    simp [hμ]
  have h2 := congrFun hfφ 1
  rw [h0, h1] at h2
  exact zero_ne_one h2

theorem sphConst (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.Rg.BcB.N3.SphConst k := by
  intro n ξ
  obtain ⟨f, hf, hf0⟩ := exists_sph (k := k) n ξ
  have hne : fixed (iP (k := k) ξ) (KO k (Fin n)) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨f, hf, hf0⟩
  obtain ⟨Y, i1, i2, σ, hirr, hfix, hsub⟩ := GlobalTheory.CuspRep.ParLaws.exists_irreducible_fixed _ _ hne
  refine ⟨Y, i1, i2, σ, ?_, hirr, hfix, hsub⟩
  obtain ⟨S, F, hF⟩ := hsub
  have hsm : IsSmooth (iP (k := k) ξ) := isSmooth_parInd _ _
  refine isSmooth_of_nhds (fun y => ?_)
  obtain ⟨s, rfl⟩ := hF y
  have ho : IsOpen {g : GL (Fin n) k | (iP ξ g) (s : _) = s} := hsm s
  have h1 : (1 : GL (Fin n) k) ∈ {g : GL (Fin n) k | (iP ξ g) (s : _) = s} := by
    rw [Set.mem_setOf_eq, map_one]
    rfl
  refine Filter.mem_of_superset (ho.mem_nhds h1) ?_
  intro g hg
  have e1 := LinearMap.congr_fun (F.isIntertwining' g) s
  simp only [LinearMap.comp_apply] at e1
  change (σ g) (F.toLinearMap s) = F.toLinearMap s
  rw [← e1]
  congr 1
  exact Subtype.ext hg

end PositivityTheory.Rg.BcB.N3.Pee
end
end

