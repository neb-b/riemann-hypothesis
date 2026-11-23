module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.Test

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem unr_lpOfChar_iff (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).unr ↔ IsUnram χ := by
  rw [WD.lpOfChar, WD.unr_mk]
  constructor
  · rintro ⟨-, H⟩ x hx
    obtain ⟨σ, rfl⟩ := ha.surj x
    have h0 : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [ord_eq_zero_iff.2 hx] at this
      omega
    have h2 := congrFun (LinearMap.congr_fun (H ⟨_, deg_eq_zero_iff.mp h0⟩) fun _ => 1) 0
    have h3 : χ (a (ineIncl h ⟨_, deg_eq_zero_iff.mp h0⟩)) = 1 := by simpa using h2
    exact h3
  · intro H
    refine ⟨rfl, fun σ => LinearMap.ext fun v => funext fun i => ?_⟩
    have : χ (a (ineIncl h σ)) = 1 := H _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq]; simp))
    simp [this]

theorem lpOfChar_unrChar (ha : IsLocalArtin h a) (c : ℂˣ) (hc) :
    WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) hc = WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
  simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]

theorem lpChar_lpSp_one (x : WD h) : x.lpChar (WD.lpSp (h := h) 1) = x := by
  have h1 : WD.lpSp (h := h) 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

end GlobalTheory.LocLanglands.Test
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Transport

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fixed_ne_bot_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

end Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def toIrrRep {n : ℕ} (π : Irr (w.adicCompletion E) n) : IrrRep (GL (Fin n) (w.adicCompletion E)) :=
  ⟨π.V, π.π, π.smooth, π.irr⟩

theorem IsRec.recLaws {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecLaws fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  have hc : ∀ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1),
      Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
    rintro χ c ⟨φ⟩
    have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
      ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
    have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
      Units.continuous_map (continuous_matrix fun i j => by
        rw [Subsingleton.elim i j]; simpa using continuous_id')
    have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
      refine MonoidHom.ext fun z => congrArg χ ?_
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩
  refine ⟨fun n π => H.dim _, fun n π π' => H.eq_iff _ _, fun r t σ τ π hπ => H.prod r t _ _ _ hπ, ?_, ?_, ?_, ?_⟩
  · intro t χ c τ h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, (H.eq_iff (toIrrRep τ) (IrrRep.det (Fin t) χ hχ)).2 h2, H.det, sumList, List.foldr_map, speh]
    simp [List.foldr_map, ← List.map_eq_flatMap]
  · intro n χ c π π' h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, ← H.twist]
    exact congrArg rc ((IrrGL.of_eq_of.2 h2).trans (IrrGL.tw_of π.π π.smooth π.irr χ hχ).symm)
  · intro n π
    rw [← H.sph]
    exact ⟨fixed_ne_bot_of_equiv (equivRep (toIrrRep π)).symm, fixed_ne_bot_of_equiv (equivRep (toIrrRep π))⟩
  · intro n π α hα
    have φ := equivRep (toIrrRep π)
    rw [H.sat (cls (toIrrRep π)) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩, WD.frobEig_diag]

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay.Model

variable {D : D7}

theorem isCuspFun_zero (V : HSp D) : IsCuspFun V fun _ => 0 := fun _ _ _ _ _ _ _ _ => by simp

def line (D : D7) : HSp D := Examples₂.posSpace Examples₂.star_isIntegral 1

def plane (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 2 ![false, true] 1 1

theorem isIsoFrame_plane (D : D7) : IsIsoFrame (plane D) (r := 1) (Matrix.of fun _ _ => 1) := by
  refine ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrFun h (0 : Fin 2)
    exact one_ne_zero this
  · have hg : ∀ i j : Fin 2, (plane D).gram i j = if i = j then (Examples₂.sgn (![false, true] i) : D.host.E) else 0 :=
      Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 2 ![false, true] 1 1
    funext a b
    change ∑ j : Fin 2, (∑ i : Fin 2, D.sp.cm.sig 1 * (plane D).gram i j) * 1 = 0
    simp [Fin.sum_univ_two, hg, Examples₂.sgn]

theorem isClosed_NI (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) :
    IsClosed (NI V C : Set (GA D V)) := by
  obtain ⟨L, hL, -⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm V C hC.2.1 hC.2.2
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : T2Space (AF D.host.F ⊗[D.host.F] D.host.E) :=
    .of_injective_continuous (f := (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun.toLinearMap)
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  rw [GlobalTheory.AutFunCompare.NI_eq]
  have hcl : IsClosed {g : GA D V |
      ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) * (C * L).map (inclR (F := D.host.F) (AF D.host.F)) = 0 ∧
      (1 - (C * L).map (inclR (F := D.host.F) (AF D.host.F))) * ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) *
        (1 - GlobalTheory.AutFunCompare.adj D.sp.cm V ((C * L).map (inclR (F := D.host.F) (AF D.host.F)))) = 0} :=
    (isClosed_eq ((hm.sub continuous_const).matrix_mul continuous_const) continuous_const).inter
    (isClosed_eq ((continuous_const.matrix_mul (hm.sub continuous_const)).matrix_mul continuous_const) continuous_const)
  convert hcl using 1
  exact Set.ext fun g => GlobalTheory.AutFunCompare.mem_unipRad_idem D.sp.cm V C L hL g

theorem not_isCuspFun_const (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    {c : ℂ} (hc : c ≠ 0) : ¬ IsCuspFun V fun _ => c := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have : LocallyCompactSpace (NI V C) := (isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : DiscreteTopology (NIQ V C) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ : Measure (NI V C) := Measure.haar
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ V C) μ
  have h0 := h r C hC μ 𝓕 inferInstance h𝓕 1
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hint : IntegrableOn (fun _ : NI V C => c) 𝓕 μ := by
    have key : ∀ N : Subgroup (GA D V), N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => c) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => c) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) μ 𝓕 inferInstance h𝓕
  have hlt : μ 𝓕 ≠ ⊤ := by
    rcases (integrableOn_const_iff (C := c)).1 hint with h | h
    · exact absurd (by simpa using h) hc
    · exact h.ne
  rw [setIntegral_const, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact ENNReal.toReal_ne_zero.2 ⟨hne, hlt⟩ h0
  · exact hc h0

theorem not_isCuspFun_one_plane (D : D7) : ¬ IsCuspFun (plane D) fun _ => 1 :=
  not_isCuspFun_const _ (isIsoFrame_plane D) one_ne_zero

end GlobalTheory.CuspDecay.Model

end
end

