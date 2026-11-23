module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import GroundTheory.PAdicHodge.NormalizedTrace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0649
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.LocSph

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

namespace SatakeVectorEventually

def MapsD {N : ℕ} (V : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E N // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E N (locGL E N w g) (f v)}

theorem iSup_range_eq {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (h : IsLocCompGL V w σ) :
    ⨆ f : MapsD V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E N, (∀ g, act o * finRep E N (locGL E N w g) = finRep E N (locGL E N w g) * act o) →
      ∀ (f : MapsD V w σ) v, act o (f.1 v) ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hV.stable o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : MapsD V w σ) ⟨v, rfl⟩
  refine (hV.irred _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : MapsD V w σ, LinearMap.range f.1) ≤ (⨆ f : MapsD V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E N w g)⁻¹)) (fun g' => by
          change finRep E N _ * _ = _ * finRep E N _
          rw [← map_mul, ← map_mul, comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E N w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E N) (infGL_comm (Unitary.toUnits k) (locGL E N w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E N w g)) f v
    exact this hφ
  · obtain ⟨f, h0, hfV, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, hfV, hf⟩ : MapsD V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact (Submodule.mem_bot ℂ).1 this

end SatakeVectorEventually


open SatakeVectorEventually in
theorem eventually_satV {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, SatV V w B := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  filter_upwards [eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.DiscLocEx.exists_isLocCompGL PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N V hV w
  have hfix : ∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) φ = φ := fun k hk => by
    obtain ⟨g, rfl⟩ := hk
    exact hw g
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [iSup_range_eq hV w σ hσ]; exact hψ
  obtain ⟨v, hv0, hv⟩ := exists_fixed_of_mem_iSup ((finRep E N).comp (locGL E N w)) σ.ρ σ.irred
    (fun f : MapsD V w σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL w (n := N) : Set _) φ h0 hfix (hmem φ hφ)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := N)) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  have key : ∀ ψ ∈ V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) ψ = ψ) → ψ ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) ψ B := fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB (fun f : MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0
  exact ⟨B, ⟨φ, hφ, key φ hφ hfix h0⟩, key⟩

end PositivityTheory.Rg.Rs.SatakeVectors

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAdm
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx

namespace PositivityTheory.Rg.Rs.PrAdm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def annZ (ψ : Sm E N) : Set (Module.End ℂ (Sm E N)) := {z | z ∈ Zalg E N ∧ z ψ = 0}

theorem cofin_annZ {ψ : Sm E N} (hψ : IsAutForm ψ) : PositivityTheory.Affgl.Cofin (annZ ψ) := by
  refine ⟨fun z hz => hz.1, ?_⟩
  let Z : Submodule ℂ (Module.End ℂ (Sm E N)) := Subalgebra.toSubmodule (Zalg E N)
  let ev : Module.End ℂ (Sm E N) →ₗ[ℂ] Sm E N := LinearMap.applyₗ ψ
  let M := Z.map ev
  have : FiniteDimensional ℂ M := by
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E N) => z ψ) '' Zalg E N)) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  let f : Z →ₗ[ℂ] M := (ev.comp Z.subtype).codRestrict M (fun z => ⟨z.1, z.2, rfl⟩)
  have hf : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 (by
    rintro ⟨_, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩)
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective hf
  refine ⟨(LinearMap.range g).map Z.subtype, inferInstance, fun z hz => ?_⟩
  let zz : Z := ⟨z, hz⟩
  set v : Z := g (f zz) with hv
  have hfg : f v = f zz := LinearMap.congr_fun hg (f zz)
  have hk : (z - v.1) ψ = 0 := by
    have := congrArg Subtype.val hfg
    change v.1 ψ = z ψ at this
    rw [LinearMap.sub_apply, this, sub_self]
  have hmem : z - v.1 ∈ annZ ψ := ⟨(Zalg E N).sub_mem hz v.2, hk⟩
  refine Submodule.mem_sup.2 ⟨v.1, ⟨v, ⟨f zz, hv.symm⟩, rfl⟩, 1 * (z - v.1),
    Submodule.subset_span ⟨1, (Zalg E N).one_mem, z - v.1, hmem, rfl⟩, by rw [one_mul, add_sub_cancel]⟩

theorem zalg_comm_act {z : Module.End ℂ (Sm E N)} (hz : z ∈ Zalg E N) (o : Op E N) : z * act o = act o * z := by
  cases o with
  | fin k => exact GlobalTheory.CuspStab.zalg_comm_fin k hz
  | cpt k => exact GlobalTheory.ZalgCpt.zalg_comm_cptRep E N k z hz
  | lie X => exact GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz

def SupSpansPsiPart (W : Submodule ℂ (Sm E N)) (ψ : Sm E N) : Submodule ℂ (Sm E N) where
  carrier := {φ | φ ∈ W ∧ ∀ z ∈ annZ ψ, z φ = 0}
  add_mem' := fun {φ φ'} h h' => ⟨W.add_mem h.1 h'.1, fun z hz => by rw [map_add (f := _), h.2 z hz, h'.2 z hz, add_zero]⟩
  zero_mem' := ⟨W.zero_mem, fun z _ => map_zero z⟩
  smul_mem' := fun c φ h => ⟨W.smul_mem c h.1, fun z hz => by rw [map_smul, h.2 z hz, smul_zero]⟩

theorem admissible_span_le (W : Submodule ℂ (Sm E N)) (ψ : Sm E N) : SupSpansPsiPart W ψ ≤ W := fun _ h => h.1

theorem mem_admissible_span_self {W : Submodule ℂ (Sm E N)} {ψ : Sm E N} (h : ψ ∈ W) : ψ ∈ SupSpansPsiPart W ψ := ⟨h, fun _ hz => hz.2⟩

theorem isStable_admissible_span {W : Submodule ℂ (Sm E N)} (hW : _root_.GlobalTheory.CuspRep.IsStable W) (ψ : Sm E N) : _root_.GlobalTheory.CuspRep.IsStable (SupSpansPsiPart W ψ) := by
  intro o φ hφ
  refine ⟨hW o φ hφ.1, fun z hz => ?_⟩
  rw [← Module.End.mul_apply, zalg_comm_act hz.1 o, Module.End.mul_apply, hφ.2 z hz, map_zero]

theorem finiteDimensional_admissible_isotypic {W : Submodule ℂ (Sm E N)} (hA : ∀ φ ∈ W, IsAutForm φ) {ψ : Sm E N} (hψ : IsAutForm ψ)
    {L : Subgroup (GL (Fin N) (Af E))} (hL : IsOpen (L : Set (GL (Fin N) (Af E)))) {U : Type} [AddCommGroup U]
    [Module ℂ U] [FiniteDimensional ℂ U] (ρ : Representation ℂ (Kinf E N) U) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ) :
    FiniteDimensional ℂ (SupSpansPsiPart W ψ ⊓ typePart L ρ : Submodule ℂ (Sm E N)) := by
  have := PositivityTheory.Rg.HF.GL.genFin E N L hL U ρ hρ (annZ ψ) (cofin_annZ hψ)
  exact Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (PositivityTheory.Affgl.genSpace L ρ (annZ ψ)))
    fun φ hφ => Submodule.subset_span
      (show φ ∈ PositivityTheory.Affgl.genSpace L ρ (annZ ψ) from ⟨hA φ hφ.1.1, hφ.2.1, hφ.2.2, hφ.1.2⟩)

theorem exists_type {χ : Sm E N} (hχ : IsAutForm χ) : ∃ L : Subgroup (GL (Fin N) (Af E)),
    IsOpen (L : Set (GL (Fin N) (Af E))) ∧ IsCompact (L : Set (GL (Fin N) (Af E))) ∧
      χ ∈ typePart L (sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E N
  let L : Subgroup (GL (Fin N) (Af E)) := U0 ⊓ GlobalTheory.DiscClosure.stabSub χ
  have hLo : IsOpen (L : Set (GL (Fin N) (Af E))) := hU0o.inter hχ.level
  refine ⟨L, hLo, hU0c.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hLo) Set.inter_subset_left,
    fun k hk => hk.2, fun g => ?_⟩
  exact GlobalTheory.Published.AutFinGL.type_of_map _ (orbSpan χ).subtype (fun _ _ => rfl)
    ⟨χ, Submodule.subset_span ⟨1, by simp⟩⟩ g

section Proj

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

theorem exists_orth (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0)
    {V : Submodule ℂ (Sm E N)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (hVW : V ≤ W) {χ : Sm E N} (hχ : χ ∈ W)
    {L : Subgroup (GL (Fin N) (Af E))} (hLo : IsOpen (L : Set (GL (Fin N) (Af E))))
    (hLc : IsCompact (L : Set (GL (Fin N) (Af E)))) {U : Type} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (ρ : Representation ℂ (Kinf E N) U) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ) (hχT : χ ∈ typePart L ρ)
    [FiniteDimensional ℂ (V ⊓ typePart L ρ : Submodule ℂ (Sm E N))] :
    ∃ v ∈ V ⊓ typePart L ρ, ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0 := by
  have hF : Function.Injective (toL2ₗ μ W h) := (injective_iff_map_eq_zero _).2 fun x e =>
    Subtype.ext (hinj x.1 x.2 (by rw [cls_mk h x.2]; exact e))
  obtain ⟨p, hpS, hp⟩ := exists_proj h hF (V ⊓ typePart L ρ) (inf_le_left.trans hVW)
  let χW : W := ⟨χ, hχ⟩
  refine ⟨(p χW).1, hpS χW, fun w hw => ?_⟩
  obtain ⟨w', hw'V, hw'L, hw'T, hinner⟩ :=
    exists_levelType_part E N μ W V h hW hA hV hVW L hLo hLc U ρ hρ ⟨w, hVW hw⟩ hw
  have hdT : (χW - p χW).1 ∈ typePart L ρ := sub_mem hχT (hpS χW).2
  have e := hinner (χW - p χW) hdT.1 hdT.2
  rw [cls_sub h hχ (p χW).2, cls_mk h hχ, cls_mk h (p χW).2, cls_mk h (hVW hw)]
  change inner ℂ (toL2ₗ μ W h χW - toL2ₗ μ W h (p χW)) (toL2ₗ μ W h ⟨w, hVW hw⟩) = 0
  rw [← map_sub, e, map_sub]
  exact hp χW w' ⟨hw'V, hw'L, hw'T⟩


omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in
theorem orth_unique (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) {V : Submodule ℂ (Sm E N)} (hVW : V ≤ W)
    {χ v v' : Sm E N} (hχ : χ ∈ W) (hv : v ∈ V) (hv' : v' ∈ V)
    (h1 : ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0) (h2 : ∀ w ∈ V, inner ℂ (cls h (χ - v')) (cls h w) = 0) :
    v = v' := by
  have hm : v' - v ∈ V := V.sub_mem hv' hv
  have e : cls h (v' - v) = cls h (χ - v) - cls h (χ - v') := by
    rw [cls_sub h (hVW hv') (hVW hv), cls_sub h hχ (hVW hv), cls_sub h hχ (hVW hv')]
    abel
  have h0 : inner ℂ (cls h (v' - v)) (cls h (v' - v)) = 0 := by
    rw [e, inner_sub_left, ← e, h1 _ hm, h2 _ hm, sub_zero]
  exact (sub_eq_zero.1 (hinj _ (hVW hm) (inner_self_eq_zero.1 h0))).symm

end Proj

end PositivityTheory.Rg.Rs.PrAdm

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
section
noncomputable section

open NumberField MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl

namespace PositivityTheory.Rg.Rs

theorem sliceTens_holds : SliceTens := by
  intro E _ _ _ r s V hV c z₁ z₂ T hT hL2 φ hφ
  refine ⟨hT.unipInv φ hφ, fun k g => ?_⟩
  have hAφ := hV.aut φ hφ

  let L := GlobalTheory.DiscClosure.stabSub φ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAφ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T φ) = T φ := fun h hh => by
    have e := hT.equiv (.fin h) φ hφ
    have hh' : finRep E (r + s) h φ = φ := hh
    change T (finRep E (r + s) h φ) = finRep E (r + s) h (T φ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T φ)
  have : FiniteDimensional ℂ S := by
    have := hAφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ φ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hT.equiv (.cpt κ) φ hφ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T φ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T φ)).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T φ, Submodule.subset_span ⟨1, by simp⟩⟩ g

  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ := fun τ u =>
    GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  choose cc hcc using hsc
  let J : Set (Module.End ℂ (Sm E (r + s))) :=
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r + s) τ u) (Polynomial.X - Polynomial.C (cc τ u))}
  have hJZ : J ⊆ Zalg E (r + s) := by
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  have hJ : Cofin J := GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic E (r + s) J hJZ fun τ u =>
    ⟨_, Polynomial.monic_X_sub_C _, τ, u, rfl⟩
  have hZ : ∀ z ∈ J, z (T φ) = 0 := by
    rintro _ ⟨τ, u, rfl⟩
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [← GlobalTheory.SpehInfChar.cap_comm_quot (fun X ψ hψ => hV.stable (.lie X) ψ hψ) T hT.equiv τ u φ hφ,
      hcc τ u φ hφ, map_smul, sub_self]
  obtain ⟨J₁, -, c₁, -, k₁, -⟩ := centre J hJ

  let L₁ := Slice1.levelOne s L g
  let ρ₁ := ρ.comp (Slice1.levK E r s)
  have := PositivityTheory.Rg.HF.GL.genFin E r L₁ (Slice1.isOpen_levelOne hLo g) S ρ₁
    (fun ℓ w => (hρ ℓ w).comp Slice1.continuous_levK) J₁ c₁
  let S₁ := tw (A2 E r) z₁ ⊓ Submodule.span ℂ (genSpace L₁ ρ₁ J₁)
  have : FiniteDimensional ℂ S₁ := Submodule.finiteDimensional_of_le inf_le_right
  let U := S₁.map (Sm E r).subtype
  obtain ⟨P, a, ha⟩ := SliceTensor.interp U
  let f : GA E r × GA E s → ℂ := fun m =>
    (T φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))
  have hleft : ∀ m₂, (fun m₁ => f (m₁, m₂)) ∈ U := by
    intro m₂
    obtain ⟨ψ, hψA, hψ, -⟩ := hT.left φ hφ k g m₂
    obtain ⟨ψ', hA', hS', e'⟩ := (hL2 φ hφ k g).1 m₂
    have hmem : ψ ∈ genSpace L₁ ρ₁ J₁ := by
      refine SliceTensor.slice_mem ρ hJZ k₁ (T φ) (hT.unipInv φ hφ) hLv hC hZ g k m₂ ψ hψA fun m₁ => ?_
      rw [hψ, infGL_comm, mul_assoc]
    have htw : ψ ∈ tw (A2 E r) z₁ := by
      refine ⟨ψ', Submodule.subset_span ⟨hA', hS'⟩, Subtype.ext (funext fun m₁ => ?_)⟩
      exact (e' m₁).trans (hψ m₁).symm
    exact ⟨ψ, ⟨htw, Submodule.subset_span hmem⟩, funext fun m₁ => hψ m₁⟩
  have hb : ∀ κ : P, ∃ b ∈ tw (A2 E r) z₁, b.1 = (a κ : GA E r → ℂ) := by
    intro κ
    obtain ⟨b, hb, e⟩ := (a κ).2
    exact ⟨b, hb.1, e⟩
  choose b hbm hbe using hb
  have hright : ∀ κ : P, ∃ ψ ∈ tw (A2 E s) z₂, ∀ m₂, ψ.1 m₂ = f (κ.1, m₂) := by
    intro κ
    obtain ⟨ψ, hA, hS, e⟩ := (hL2 φ hφ k g).2 κ.1
    exact ⟨_, ⟨ψ, Submodule.subset_span ⟨hA, hS⟩, rfl⟩, e⟩
  choose q hqm hqe using hright
  have hf : f = ∑ κ : P, fun m : GA E r × GA E s => (b κ).1 m.1 * (q κ).1 m.2 := by
    funext m
    have e := congrFun (ha _ (hleft m.2)) m.1
    rw [Finset.sum_apply]
    rw [Finset.sum_apply] at e
    refine e.trans (Finset.sum_congr rfl fun κ _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hbe, hqe]
    ring
  change f ∈ _
  rw [hf]
  exact Submodule.sum_mem _ fun κ _ => Submodule.subset_span ⟨b κ, hbm κ, q κ, hqm κ, rfl⟩

end PositivityTheory.Rg.Rs

end
end

