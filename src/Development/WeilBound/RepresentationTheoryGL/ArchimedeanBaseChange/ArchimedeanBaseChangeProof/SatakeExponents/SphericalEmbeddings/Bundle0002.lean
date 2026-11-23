module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageB

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseExp
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseExp

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_map_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    ∃ f : π.IntertwiningMap (indB (ofChar μ)), f ≠ 0 := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hl0 (LinearMap.ext fun x => ?_)⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
  have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
  rw [h2, h1, h0]
  rfl

theorem expSph : ExpSph k := by
  intro n V _ _ π hs hi hsph
  have hadm : IsAdmissible π := (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi
  have hI : fixed π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsph
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨χ, l, hl0, hl, hχ⟩ := GlobalTheory.SatakeExists.exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  obtain ⟨f, hf⟩ := exists_map_of_eigenform hadm.1 (χ * δ⁻¹) l hl0 fun t x => by
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  refine ⟨α, ?_⟩
  show ∃ f : π.IntertwiningMap (indB (ofChar (torusChar fun i => unrChar k (α i)))), f ≠ 0
  rw [hα]
  exact ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.PseExp
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory

namespace PositivityTheory.Rg.BcB.N3.PseSat

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (hi : π.IsIrreducible) (f : π.IntertwiningMap σ)
    (hf : f ≠ 0) : Function.Injective f := by
  have := hi
  let S : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    simp only [LinearMap.mem_ker] at hv
    simp [show f v = 0 from hv]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · intro a b hab
    have : a - b ∈ S.toSubmodule := by
      show f.toLinearMap (a - b) = 0
      rw [map_sub]
      exact sub_eq_zero.2 hab
    rw [h] at this
    exact sub_eq_zero.1 this
  · exfalso
    apply hf
    ext v
    have : v ∈ S.toSubmodule := by rw [h]; trivial
    exact this

theorem isSubquotient_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Injective f) :
    IsSubquotient π σ := by
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨π g v, by simpa using Representation.IntertwiningMap.isIntertwining _ _ f g v⟩⟩
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  refine ⟨R, ⟨e.symm.toLinearMap, fun g => ?_⟩, e.symm.surjective⟩
  ext ⟨w, v, rfl⟩
  apply e.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  show _ = f (π g (e.symm ⟨f v, v, rfl⟩))
  have h1 : e.symm ⟨f v, v, rfl⟩ = v := e.symm_apply_eq.2 rfl
  rw [h1, f.isIntertwining]
  rfl

theorem satPerm : SatPerm k := by
  intro n ξ η V _ _ π hs hi hsph hq ⟨f, hf⟩
  have hinj := injective_of_ne_zero hi f hf
  have hq' := isSubquotient_of_injective f hinj
  borelize (GL (Fin n) k)
  have h1 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ξ hq (μ := Measure.haar)
  have h2 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) η hq' (μ := Measure.haar)
  have hK := (GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors π).1 hsph
  exact GroundTheory.Automorphic.Spherical.satakeParameter_unique hK h1 h2

end PositivityTheory.Rg.BcB.N3.PseSat
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageC
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_append {r t : ℕ} (a : Fin r → ℂˣ) (b : Fin t → ℂˣ) :
    (fun i => unrChar k (Fin.append a b i)) = Fin.append (fun i => unrChar k (a i)) (fun i => unrChar k (b i)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp

set_option maxHeartbeats 2000000 in
theorem prin_append {r t : ℕ} (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :
    Nonempty ((prod₂ (prinSeries ψ₁) (prinSeries ψ₂)).Equiv (prinSeries (Fin.append ψ₁ ψ₂))) := by
  obtain ⟨E1⟩ := GlobalTheory.SmGL.PrinProd.stage_one (k := k) ψ₁ ψ₂
  obtain ⟨E2⟩ := GlobalTheory.SmGL.PrinProd.stage_two (k := k) ψ₁ ψ₂
  exact ⟨E1.trans E2⟩

set_option maxHeartbeats 2000000 in
theorem iP_append (r t : ℕ) (A : Fin r → ℂˣ) (B : Fin t → ℂˣ) :
    Nonempty ((prod₂ (iP (k := k) A) (iP (k := k) B)).Equiv (iP (k := k) (Fin.append A B))) := by
  have key : ∀ χ : Fin (r + t) → kˣ →* ℂˣ,
      χ = Fin.append (fun i => unrChar k (A i)) (fun i => unrChar k (B i)) →
      Nonempty ((prod₂ (prinSeries fun i => unrChar k (A i))
        (prinSeries fun i => unrChar k (B i))).Equiv (prinSeries χ)) := by
    rintro χ rfl
    exact prin_append _ _
  exact key _ (unrChar_append A B)

theorem mainGen {r t : ℕ} {VA VB Vc Vc' Vi Vi' Vo Vo' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB]
    [Module ℂ VB] [AddCommGroup Vc] [Module ℂ Vc] [AddCommGroup Vc'] [Module ℂ Vc'] [AddCommGroup Vi] [Module ℂ Vi]
    [AddCommGroup Vi'] [Module ℂ Vi'] [AddCommGroup Vo] [Module ℂ Vo] [AddCommGroup Vo'] [Module ℂ Vo']
    (πA : Representation ℂ (GL (Fin r) k) VA) (πB : Representation ℂ (GL (Fin t) k) VB)
    {πc : Representation ℂ (GL (Fin 2) k) Vc} {πc' : Representation ℂ (GL (Fin 2) k) Vc'}
    {πi : Representation ℂ (GL (Fin (2 + t)) k) Vi} {πi' : Representation ℂ (GL (Fin (2 + t)) k) Vi'}
    {πo : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo} {πo' : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo'}
    (Ei : (prod₂ πc πB).Equiv πi) (Ei' : (prod₂ πc' πB).Equiv πi') (Eo : (prod₂ πA πi).Equiv πo)
    (Eo' : (prod₂ πA πi').Equiv πo') (T : πc.IntertwiningMap πc') (hT : KInj k T) :
    ∃ T' : πo.IntertwiningMap πo', KInj k T' := by
  let M : πi.IntertwiningMap πi' :=
    Ei'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapL T πB).comp Ei.symm.toIntertwiningMap)
  have hM : KInj k M :=
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapL T hT _)) (kinj_equiv _)
  exact ⟨Eo'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapR πA M).comp Eo.symm.toIntertwiningMap),
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapR _ M hM)) (kinj_equiv _)⟩

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

