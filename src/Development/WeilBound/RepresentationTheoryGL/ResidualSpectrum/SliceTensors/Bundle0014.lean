module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import GroundTheory.PAdicHodge.ACrisBdR
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapD
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def res (y : GA E (r + s)) : (GA E (r + s) → ℂ) →ₗ[ℂ] (GA E r × GA E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun m => lev (Ad E) r s m * y

theorem res_apply (y : GA E (r + s)) (F : GA E (r + s) → ℂ) (m : GA E r × GA E s) :
    res y F m = F (lev (Ad E) r s m * y) := rfl

structure Good (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (f₁ : Sm E r →ₗ[ℂ] Sm E r)
    (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Prop where
  hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁
  hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂
  hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)
  hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)

theorem good_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁) (hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂) :
    Good U₁ U₂ LinearMap.id LinearMap.id :=
  ⟨hU₁, hU₂, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

def IsInd (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) (F : GA E (r + s) → ℂ) : Prop :=
  (∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x) ∧ ∀ k g, res (cf (r + s) k g) F ∈ tens2 U₁ U₂

def indSub (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | IsInd U₁ U₂ F.1}
  add_mem' := by
    intro F G hF hG
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change F.1 _ + G.1 _ = F.1 x + G.1 x
      rw [hF.1, hG.1]
    · exact add_mem (hF.2 k g) (hG.2 k g)
  zero_mem' := by
    exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  smul_mem' := by
    intro c F hF
    refine ⟨fun u x => ?_, fun k g => ?_⟩
    · change c * F.1 _ = c * F.1 x
      rw [hF.1]
    · exact Submodule.smul_mem _ c (hF.2 k g)

theorem exists_dec (x : GA E (r + s)) :
    ∃ q : (BlockIx (r + s) r → Ad E) × (GA E r × GA E s) × Kinf E (r + s) × GL (Fin (r + s)) (Af E),
      x = unip q.1 * lev (Ad E) r s q.2.1 * cf (r + s) q.2.2.1 q.2.2.2 := by
  obtain ⟨u, m, k, g, h⟩ := exists_decomp x
  exact ⟨(u, m, k, g), h⟩

def ind (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E (r + s) → ℂ) :=
  LinearMap.pi fun x => LinearMap.proj (exists_dec x).choose.2.1 ∘ₗ tensOp f₁ f₂ ∘ₗ
    res (cf (r + s) (exists_dec x).choose.2.2.1 (exists_dec x).choose.2.2.2)

theorem cf_inv (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : (cf a k g)⁻¹ = cf a k⁻¹ g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [cf_mul, mul_inv_cancel, mul_inv_cancel, cf, map_one, map_one, map_one, mul_one]

theorem cf_one (a : ℕ) : cf a (1 : Kinf E a) 1 = 1 := by
  rw [cf, map_one, map_one, map_one, mul_one]

theorem D.unip_add' {R : Type} [CommRing R] {a r : ℕ} (x y : BlockIx a r → R) : unip (x + y) = unip x * unip y := by
  simp only [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_add x y

theorem D.indep {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    {u u' : BlockIx (r + s) r → Ad E} {m m' : GA E r × GA E s} {k k' : Kinf E (r + s)} {g g' : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m * cf (r + s) k g = unip u' * lev (Ad E) r s m' * cf (r + s) k' g') :
    tensOp f₁ f₂ (res (cf (r + s) k g) F) m = tensOp f₁ f₂ (res (cf (r + s) k' g') F) m' := by
  obtain ⟨v, hv⟩ := lev_mul_unip m⁻¹ (-u + u')
  have hu : unip (-u) * unip u = (1 : GA E (r + s)) := by rw [← D.unip_add', neg_add_cancel, unip_zero]
  have e1 : cf (r + s) k g = unip v * lev (Ad E) r s (m⁻¹ * m') * cf (r + s) k' g' := by
    rw [map_mul, ← mul_assoc, ← hv, D.unip_add']
    calc cf (r + s) k g = lev (Ad E) r s m⁻¹ * (unip (-u) * (unip u * lev (Ad E) r s m * cf (r + s) k g)) := by
          rw [← mul_assoc (unip (-u)), ← mul_assoc (unip (-u)), hu, one_mul, ← mul_assoc, ← map_mul, inv_mul_cancel,
            map_one, one_mul]
      _ = _ := by rw [h]; simp only [mul_assoc]
  have e2 : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (g * g'⁻¹) := by
    rw [← cf_mul, ← cf_inv, e1, mul_inv_cancel_right]
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf e2
  have e3 : res (cf (r + s) k g) F = fun z => res (cf (r + s) k' g') F (z.1 * cf r k₁ g₁, z.2 * cf s k₂ g₂) := by
    funext z
    obtain ⟨w, hw⟩ := lev_mul_unip z v
    rw [res_apply, res_apply, e1, ← mul_assoc, ← mul_assoc, hw, mul_assoc, mul_assoc, hF.1, ← mul_assoc, ← map_mul, hm]
    rfl
  rw [e3, tensOp_translate H.hU₁ H.hU₂ H.hf₁ H.hf₂ (hF.2 k' g')]
  have e4 : m' = (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
    rw [← mul_inv_cancel_left m m', hm]
    rfl
  rw [e4]

theorem ind_apply {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ind f₁ f₂ F (unip u * lev (Ad E) r s m * cf (r + s) k g) = tensOp f₁ f₂ (res (cf (r + s) k g) F) m := by
  have hq := (exists_dec (unip u * lev (Ad E) r s m * cf (r + s) k g)).choose_spec
  exact (D.indep H hF hq).symm

theorem ind_left {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (u : BlockIx (r + s) r → Ad E) (x : GA E (r + s)) : ind f₁ f₂ F (unip u * x) = ind f₁ f₂ F x := by
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [← mul_assoc, ← mul_assoc, ← D.unip_add', ind_apply H hF, ind_apply H hF]

theorem ind_levi {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    res (cf (r + s) k g) (ind f₁ f₂ F) = tensOp f₁ f₂ (res (cf (r + s) k g) F) := by
  funext m
  have := ind_apply H hF 0 m k g
  rw [unip_zero, one_mul] at this
  exact this

theorem isInd_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E (r + s) → ℂ}
    (hF : IsInd U₁ U₂ F) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    IsInd U₁ U₂ fun x => F (x * cf (r + s) k g) := by
  refine ⟨fun u x => by beta_reduce; rw [mul_assoc, hF.1], fun k' g' => ?_⟩
  convert hF.2 (k' * k) (g' * g) using 1
  funext m
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ind_rt {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F)
    (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (x : GA E (r + s)) :
    ind f₁ f₂ (fun y => F (y * cf (r + s) k g)) x = ind f₁ f₂ F (x * cf (r + s) k g) := by
  obtain ⟨v, m, k', g', rfl⟩ := exists_decomp x
  rw [ind_apply H (isInd_rt hF k g), mul_assoc _ (cf (r + s) k' g'), cf_mul, ind_apply H hF]
  refine congrArg (fun G => tensOp f₁ f₂ G m) (funext fun z => ?_)
  rw [res_apply, res_apply, mul_assoc, cf_mul]

theorem ext_res {F F' : GA E (r + s) → ℂ} (hF : ∀ (u : BlockIx (r + s) r → Ad E) x, F (unip u * x) = F x)
    (hF' : ∀ (u : BlockIx (r + s) r → Ad E) x, F' (unip u * x) = F' x)
    (e : ∀ k g, res (cf (r + s) k g) F = res (cf (r + s) k g) F') : F = F' := by
  funext x
  obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
  rw [mul_assoc, hF, hF']
  exact congrFun (e k g) m

theorem ind_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁) (hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂)
    {F : GA E (r + s) → ℂ} (hF : IsInd U₁ U₂ F) : ind LinearMap.id LinearMap.id F = F := by
  refine ext_res (ind_left (good_id hU₁ hU₂) hF) hF.1 fun k g => ?_
  rw [ind_levi (good_id hU₁ hU₂) hF, tensOp_id (hF.2 k g)]

theorem finVec_rt {F : Sm E (r + s)} (hF : F ∈ finVec (cptRep E (r + s))) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : rt E (r + s) (cf (r + s) k g) F ∈ finVec (cptRep E (r + s)) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)) := hF
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k' => cptRep E (r + s) k' (rt E (r + s) (cf (r + s) k g) F)))
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k F)).map
    (rt E (r + s) (finGL E (r + s) g))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k' * k, rfl⟩, Subtype.ext (funext fun x => ?_)⟩
  change F.1 (x * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits (k' * k))) =
    F.1 (x * infGL E (r + s) (Unitary.toUnits k') * cf (r + s) k g)
  rw [cf, mul_assoc x, ← infGL_comm, map_mul, map_mul]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatHerm
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs

namespace SatakeHermitian

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_locRepD {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LGrp.IsUnitarisable (GlobalTheory.DiscLocEx.locRepD hV.stable w) := by
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := GlobalTheory.DiscreteUnit.countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  refine GlobalTheory.DiscreteUnit.isUnitarisable_of_embedding (Γ := latticeGL E N) (GlobalTheory.DiscLocEx.locRepD hV.stable w)
    (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp V.subtype) (Subtype.val_injective.comp Subtype.val_injective)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N v.1 (hV.aut _ v.2).level)
    (fun v => GlobalTheory.DiscreteUnit.left_latticeGL (hV.aut _ v.2) (hV.sqInt _ v.2)) (fun v => (hV.sqInt _ v.2).2)
    fun g v x => rfl
  exact GlobalTheory.DiscreteUnit.modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (GlobalTheory.DiscreteUnit.cornerGL_transInv (sLoc E w) g)).trans
      (GlobalTheory.DiscreteUnit.cornerGL_transInv (sFin E) _)) g

theorem herm_of_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : B.map (fun b => (star b)⁻¹) = B := by
  have e := congrArg (Multiset.map (fun b : ℂˣ => b⁻¹)) h
  rw [Multiset.map_map, Multiset.map_map] at e
  simpa [Function.comp_def] using e

theorem herm_of_isSatVec {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {B : Multiset ℂˣ} {φ : Sm E N} (hφ : φ ∈ V)
    (h : GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B) : B.map (fun b => (star b)⁻¹) = B := by
  have h' : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφ⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E N).comp (locGL E N w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective h
  exact herm_of_star (GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable E w N V _ _ B (isUnitarisable_locRepD hV w) h')

end SatakeHermitian

open SatakeHermitian in
theorem satHerm_holds : SatHerm := by
  intro E _ _ _ N w B
  refine ⟨fun V hV hS => ?_, fun π hN hu hn hB => ?_⟩
  · obtain ⟨φ, hφ, h⟩ := hS.1
    exact herm_of_isSatVec hV hφ h
  · have hD : IsDiscrete π.V := PositivityTheory.RSHS.L1.cuspDiscrete E N hN π hu hn
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
    have h1 := hx.map (ρ' := (finRep E N).comp (locGL E N w)) π.V.subtype (fun _ _ => rfl)
      (fun e => hx.1 (Subtype.ext e))
    exact herm_of_isSatVec hD x.2 h1

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStages
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

open InductionInStages ParabolicProjection in
theorem stages_of (hI : IndMap) : Stages := by
  intro E _ _ _ r s a d₁ d₂ V V₁ V₂ π hV hV₁ hV₂ hemb h₁ h₂
  obtain ⟨T, hTmem, hTinj, hTeq⟩ := hemb
  obtain ⟨hs₁, ν₁, hν₁, f₁, hf₁mem, hf₁inj, hf₁eq⟩ := h₁
  obtain ⟨hs₂, ν₂, hν₂, f₂, hf₂mem, hf₂inj, hf₂eq⟩ := h₂
  set z₁ : ℂ := ((s : ℂ) - d₂) / 2 with hz₁
  set z₂ : ℂ := ((d₁ : ℂ) - r) / 2 with hz₂
  obtain ⟨T', hT'eq, hT'u, hT'sl⟩ := hI E r s V (tw V₁ z₁) (tw V₂ z₂) T (twMap r z₁ f₁) (twMap s z₂ f₂) hV.stable hV.aut
    (isStable_tw hV₁.stable z₁) (isStable_tw hV₂.stable z₂) hTeq hTmem (twMap_equiv hV₁.stable hf₁eq)
    (twMap_equiv hV₂.stable hf₂eq)
  have hr : r = d₁ * a := sum_const_eq hs₁
  have hs : s = d₂ * a := sum_const_eq hs₂
  have H : ∑ _ : Fin (d₁ + d₂), a = r + s := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; rw [hr, hs]; ring
  let ν : Fin (d₁ + d₂) → HChar E := fun i =>
    Model.absC E ((-spehExp (d₁ + d₂) i + a * spehExp (d₁ + d₂) i : ℝ) : ℂ)

  have hsl : ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r)
      (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ tw V₁ z₁) ∧ (∀ i, ψ₂ i ∈ tw V₂ z₂) ∧
      (∀ m : GA E r × GA E s, (T φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∧
      ∀ m : GA E r × GA E s, (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (twMap r z₁ f₁ (ψ₁ i)).1 m.1 * (twMap s z₂ f₂ (ψ₂ i)).1 m.2 := by
    intro φ hφ k g
    obtain ⟨n, ψ₁, ψ₂, h1, h2, he⟩ := tensor_pair_finite_sum ((hTmem φ hφ).2 k g)
    exact ⟨n, ψ₁, ψ₂, h1, h2, he, hT'sl φ hφ k g n ψ₁ ψ₂ h1 h2 he⟩
  refine ⟨H, ν, fun i => isAbsPow_absC _, T', fun φ hφ => ?_, ?_, hT'eq⟩
  · refine mem_indForms_of_slices hs₁ hs₂ H (fam₁ := fun b => π.twist (ν₁ b)) (fam₂ := fun b => π.twist (ν₂ b))
      (z₁ := z₁) (z₂ := z₂) (fun b => ?_) (fun b => ?_) (hT'u φ hφ) (fun k g => ?_) ?_ ?_
    · rw [← CuspSub.twist_mul, eq_absC (hν₁ b), absC_mul]
      refine congrArg (fun x => π.twist (Model.absC E x)) ?_
      simp only [spehExp, Fin.val_castAdd, hz₁, hs]
      push_cast; ring
    · rw [← CuspSub.twist_mul, eq_absC (hν₂ b), absC_mul]
      refine congrArg (fun x => π.twist (Model.absC E x)) ?_
      simp only [spehExp, Fin.val_natAdd, hz₂, hr]
      push_cast; ring
    · obtain ⟨n, ψ₁, ψ₂, h1, h2, -, he⟩ := hsl φ hφ k g
      exact ⟨n, fun i => twMap r z₁ f₁ (ψ₁ i), fun i => twMap s z₂ f₂ (ψ₂ i), fun i => twMap_mem hf₁mem _ (h1 i),
        fun i => twMap_mem hf₂mem _ (h2 i), he⟩
    · refine isOpen_stab_of_mem_nhds (finRep E (r + s)) (T' φ) (Filter.mem_of_superset
        ((hV.aut φ hφ).level.mem_nhds (by simp)) fun k hk => ?_)
      have hk' : finRep E (r + s) k φ = φ := hk
      exact (hT'eq (.fin k) φ hφ).symm.trans (congrArg T' hk')
    · have := (hV.aut φ hφ).kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)).map T')
        (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, hT'eq (.cpt k) φ hφ⟩
  · obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := (Submodule.ne_bot_iff V).1 hV.ne_bot
    refine inj_of_irred hV hT'eq ⟨φ₀, hφ₀, fun h0 => ?_⟩
    have hTne : T φ₀ ≠ 0 := fun h => hφ₀ne (hTinj φ₀ hφ₀ h)
    obtain ⟨k, g, m, hne⟩ := exists_slice_ne hTne (hTmem φ₀ hφ₀).1
    obtain ⟨n, ψ₁, ψ₂, h1, h2, he, he'⟩ := hsl φ₀ hφ₀ k g
    rw [he m] at hne
    have hθ₁ := sum_left_ne hne
    have hθ₁m : ∑ i, (ψ₂ i).1 m.2 • ψ₁ i ∈ tw V₁ z₁ := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i)
    obtain ⟨b₁, hb₁⟩ := step_left (twMap r z₁ f₁) (fun h => hθ₁ (twMap_ne hf₁inj _ hθ₁m h))
    have hθ₂ := sum_right_ne (ψ₁ := fun i => twMap r z₁ f₁ (ψ₁ i)) hb₁
    have hθ₂m : ∑ i, (twMap r z₁ f₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw V₂ z₂ :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h2 i)
    obtain ⟨b₂, hb₂⟩ := step_right (twMap s z₂ f₂) (fun h => hθ₂ (twMap_ne hf₂inj _ hθ₂m h))
    refine hb₂ ?_
    have := he' (b₁, b₂)
    rw [h0] at this
    exact this.symm

end PositivityTheory.Rg.Rs

end
end

