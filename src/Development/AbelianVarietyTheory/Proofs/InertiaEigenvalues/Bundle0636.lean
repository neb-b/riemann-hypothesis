module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousResI
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem countable_numberField_type (K : Type) [Field K] [NumberField K] : Countable K := by
  let b := Module.finBasis ℚ K
  exact (b.equivFun.toEquiv.injective).countable

theorem lag_countable : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  intro D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  let M := (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)
  haveI : Countable (Submodule D.host.E M) := by
    have hs : Function.Surjective (fun s : Finset M => Submodule.span D.host.E (s : Set M)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  unfold Lag
  infer_instance

end GlobalTheory.RawLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.BadPlace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def datP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (e : AE D) : WO (Vc D i) (Wc D i) → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
      omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
    else 0

end GlobalTheory.BadPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.UnitaryBC
open GlobalTheory.CuspRep.LocEx

namespace GlobalTheory.DiscLocEx

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (o : Op E a) : Module.End ℂ V := (act o).restrict (hV o)

def finPartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) : Representation ℂ (GL (Fin a) (Af E)) V :=
  GlobalTheory.PRep.sub (finRep E a) V fun k => hV (.fin k)

def locRepD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  (finPartD hV).comp (locGL E a w)

theorem isSmooth_finPartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ) :
    IsSmooth (finPartD hV) := fun φ => by
  convert (ha _ φ.2).level using 1
  ext k
  exact Subtype.ext_iff

theorem isSmooth_locRepD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ)
    (w : HeightOneSpectrum (𝓞 E)) : IsSmooth (locRepD hV w) := fun φ =>
  (isSmooth_finPartD hV ha φ).preimage (CuspSub.continuous_locGL w)

theorem exists_scalarD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem nullPart_opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (o : Op E a) {x : V} (hx : x ∈ nullPart (locRepD hV w) K) : opD hV o x ∈ nullPart (locRepD hV w) K := by
  cases o with
  | fin k =>
    have h1 := nullPart_act _ K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm _ K
      (finPartD hV ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
      simp only [locRepD, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        LocUniq.comm_locGL w (map_pLoc_inv_mul w k)]) hx)
    rwa [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
  | cpt k =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem eq_bot_of_fixedD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    {K : Subgroup (GL (Fin a) (w.adicCompletion E))} (hK : IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))))
    {φ : V} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (locRepD hV.stable w) K) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, locRepD hV.stable w g v ∈ W) (h : W ⊓ fixed (locRepD hV.stable w) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective V.injective_subtype
  rcases hV.irred ((nullPart (locRepD hV.stable w) K).map V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, nullPart_opD hV.stable w K o hx, rfl⟩) with h1 | h1
  · have h2 : nullPart (locRepD hV.stable w) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK W hW h)
  · have h2 : nullPart (locRepD hV.stable w) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK hφ (h2 ▸ Submodule.mem_top)) h0

def typePartD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) : Submodule ℂ V where
  carrier := {ψ | (∀ k ∈ L, GeneralLinearGroup.map (pLoc E w) k = 1 → finPartD hV k ψ = ψ) ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k h1 h2 => by rw [map_add (f := _), hx.1 k h1 h2, hy.1 k h1 h2],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k h1 h2 => by rw [map_smul, hx.1 k h1 h2],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem typePartD_act {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (w.adicCompletion E))
    (x : V) (hx : x ∈ typePartD hV w L ρ) : locRepD hV w g x ∈ typePartD hV w L ρ := by
  refine ⟨fun k h1 h2 => ?_, fun y => ?_⟩
  · rw [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, LocUniq.comm_locGL w h2, map_mul,
      Module.End.mul_apply, hx.1 k h1 h2]
  · convert hx.2 (y * finGL E a (locGL E a w g)) using 2 with k
    change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
    rw [mul_assoc, mul_assoc, infGL_comm]

theorem finiteDimensional_typePartD (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (hK : IsOpen (K : Set (GL (Fin a) (w.adicCompletion E)))) :
    FiniteDimensional ℂ ↥(typePartD hV.stable w L ρ ⊓ fixed (locRepD hV.stable w) K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ V, cap τ u φ = c • φ := fun τ u =>
    exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w)))
    (hL.inter ((hK.inter (hL.preimage (CuspSub.continuous_locGL w))).preimage (continuous_map_pLoc w))) W ρ hρ c
  refine FiniteDimensional.of_injective ((V.subtype ∘ₗ (typePartD hV.stable w L ρ ⊓
    fixed (locRepD hV.stable w) K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms
      (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w))) ρ c))
    fun v => Submodule.subset_span ⟨hV.aut _ v.1.2, fun k hk => ?_, v.2.1.2, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 := v.2.1.1 _ (L.mul_mem (L.inv_mem hk.2.2) hk.1) (map_pLoc_inv_mul w k)
  have h2 := mem_fix.1 v.2.2 _ hk.2.1
  have h3 : finPartD hV.stable k v.1 = v.1 := by
    rw [← mul_inv_cancel_left (locGL E a w (GeneralLinearGroup.map (pLoc E w) k)) k, map_mul, Module.End.mul_apply, h1]
    exact h2
  exact congrArg Subtype.val h3

theorem exists_irred_sub (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧
      ∀ g v, f (σ.ρ g v) = locRepD hV.stable w g (f v)) ∧ IsAdmissible σ.ρ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h0' : (⟨φ, hφ⟩ : V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab (finPartD hV.stable) ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) :=
    isSmooth_finPartD hV.stable hV.aut _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have : FiniteDimensional ℂ (orbSpan φ) := (hV.aut φ hφ).kfin
  refine exists_irred (isSmooth_locRepD hV.stable hV.aut w) ho (eq_bot_of_fixedD hV w hc h0' (mem_fix.2 hK))
    (typePartD hV.stable w (stab (finPartD hV.stable) ⟨φ, hφ⟩) (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)))
    (typePartD_act hV.stable w _ _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ⟨fun k hk _ => hk, ?_⟩, h0'⟩)
    (finiteDimensional_typePartD h hV w hL (isContRep_sub _ _))
  exact AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
    ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩

end GlobalTheory.DiscLocEx


open GlobalTheory.DiscSpec GlobalTheory.SmGL in
theorem GlobalTheory.DiscLocEx.exists_isLocCompGL : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V →
    ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  intro h E _ _ _ N V hV w
  obtain ⟨σ, ⟨f, hf0, hf⟩, -⟩ := GlobalTheory.DiscLocEx.exists_irred_sub h hV w
  refine ⟨σ, V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun g v => congrArg Subtype.val (hf g v)⟩
  exact LinearMap.congr_fun e v
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh MeasureTheory Matrix

namespace GlobalTheory.DiscreteUnit

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [Countable Γ]

theorem lintegral_lt_top {μ μ' : Measure G} [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {F F' : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hF' : IsFundamentalDomain Γ F' μ') {φ : G → ENNReal}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (h : ∫⁻ g in F', φ g ∂μ' < ⊤) : ∫⁻ g in F, φ g ∂μ < ⊤ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hF2 : IsFundamentalDomain Γ F' μ := hF'.mono (Measure.absolutelyContinuous_isHaarMeasure μ μ')
  rw [hF.setLIntegral_eq hF2 φ fun γ g => hφ γ γ.2 g, e, Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

theorem integral_mul_right {μ : Measure G} [μ.IsHaarMeasure] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {φ : G → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) {x : G} (hx : Measure.modularCharacter x = 1) :
    ∫ g in F, φ (g * x) ∂μ = ∫ g in F, φ g ∂μ := by
  have hm : MeasurePreserving (fun g => g * x) μ μ :=
    ⟨measurable_mul_const x, by rw [GlobalTheory.LevelUnimod.map_mul_right_eq, hx, one_smul]⟩
  have hF2 : IsFundamentalDomain Γ ((fun g => g * x) ⁻¹' F) μ :=
    hF.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc γ.1 g x
  rw [hF.setIntegral_eq hF2 (f := fun g => φ (g * x)) fun γ g => by
    change φ (γ.1 * g * x) = _
    rw [mul_assoc, hφ γ γ.2]]
  exact hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding φ F

theorem isUnitarisable_of_embedding {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (ι : H → G) (hι : ∀ h, Measure.modularCharacter (ι h) = 1) (f : X →ₗ[ℂ] (G → ℂ)) (hf : Function.Injective f)
    (hc : ∀ v, Continuous (f v)) (hl : ∀ v, ∀ γ ∈ Γ, ∀ g, f v (γ * g) = f v g)
    (h2 : ∀ v, ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∫⁻ g in F, ‖f v g‖ₑ ^ 2 ∂μ < ⊤)
    (hρ : ∀ h v g, f (ρ h v) g = f v (g * ι h)) : IsUnitarisable ρ := by
  obtain ⟨μ, F, hμ, hF, -⟩ := h2 0
  have hm : ∀ v, MemLp (f v) 2 (μ.restrict F) := fun v => by
    obtain ⟨μ', F', hμ', hF', h⟩ := h2 v
    have h3 := lintegral_lt_top hF hF' (fun γ hγ g => by rw [hl v γ hγ g]) h
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    · simpa using h3
    · exact (hc v).aestronglyMeasurable
  have hi : ∀ v w, Integrable (fun g => f v g * starRingEnd ℂ (f w g)) (μ.restrict F) := fun v w =>
    (hm v).integrable_mul (hm w).star
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ g in F, f v g * starRingEnd ℂ (f w g) ∂μ)
    (fun v v' w => ?_) (fun c v w => ?_) (fun v w w' => ?_) (fun c v w => ?_), fun v w => ?_, fun v hv => ?_,
    fun h v w => ?_⟩
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [add_mul]
  · simp [mul_assoc, integral_const_mul]
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [mul_add]
  · simp [mul_left_comm _ (starRingEnd ℂ c), integral_const_mul]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]
    simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hi2 : Integrable (fun g => Complex.normSq (f v g)) (μ.restrict F) := by
      simpa [Complex.mul_conj] using (hi v v).re
    refine (integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi2).2 (pos_iff_ne_zero.2 fun h0 => hv ?_)
    have ho : IsOpen (Function.support fun g => Complex.normSq (f v g)) :=
      (Complex.continuous_normSq.comp (hc v)).isOpen_support
    rw [Measure.restrict_apply ho.measurableSet] at h0
    have h4 := hF.measure_zero_of_invariant _ (fun γ => by
      ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
      change Complex.normSq (f v ((γ⁻¹ : Γ).1 * g)) ≠ 0 ↔ _
      rw [hl v _ (γ⁻¹).2]) h0
    have h5 := Function.support_eq_empty_iff.1 (ho.measure_eq_zero_iff μ |>.1 h4)
    refine hf (funext fun g => ?_)
    rw [map_zero]
    exact Complex.normSq_eq_zero.1 (congrFun h5 g)
  · simp only [LinearMap.mk₂'ₛₗ_apply, hρ]
    exact integral_mul_right hF (φ := fun g => f v g * starRingEnd ℂ (f w g))
      (fun γ hγ g => by rw [hl v γ hγ, hl w γ hγ]) (hι h)

end General

def transInv (A : Type) [CommRing A] (n : ℕ) : GL (Fin n) A ≃* GL (Fin n) A where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  invFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change ((g * h)⁻¹).valᵀ = (g⁻¹).valᵀ * (h⁻¹).valᵀ
    rw [← transpose_mul, _root_.mul_inv_rev, Units.val_mul])

theorem continuous_transInv (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Continuous (transInv A n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem cornerGL_transInv {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (s : R →ₙ+* S) (g : GL (Fin n) R) :
    cornerGL n s (transInv R n g) = transInv S n (cornerGL n s g) := by
  ext i j
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin n) (Fin n) S) j i - s ((1 : Matrix (Fin n) (Fin n) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm]

theorem modular_eq_one {k S : Type} [Field k] [Infinite k] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n : ℕ}
    [LocallyCompactSpace (GL (Fin n) S)] [SecondCountableTopology (GL (Fin n) S)] (ι : GL (Fin n) k →* GL (Fin n) S)
    (h : ∀ g, ι (transInv k n g) = transInv S n (ι g)) (g : GL (Fin n) k) : Measure.modularCharacter (ι g) = 1 := by
  borelize (GL (Fin n) S)
  refine GlobalTheory.gl_character_eq_one_of_transpose_inv _ _ (Measure.modularCharacter.comp ι) (fun g g' e => ?_) g
  obtain rfl : g' = transInv _ n g := Units.ext e
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact GlobalTheory.LevelUnimod.modular_aut _ (continuous_transInv _ n) (continuous_transInv _ n) _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem countable_latticeGL : Countable (latticeGL E N) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin N) (Fin N) E) := inferInstanceAs (Countable (Fin N → Fin N → E))
  haveI : Countable (GL (Fin N) E) := Units.val_injective.countable
  let f : FreeGroup (Option (GL (Fin N) E)) →* GA E N :=
    FreeGroup.lift fun o => o.elim (splitCentre E N 1) (ratGL E N)
  have h : latticeGL E N ≤ f.range := sup_le
    (by rintro _ ⟨γ, rfl⟩; exact ⟨.of (some γ), FreeGroup.lift_apply_of⟩)
    (Subgroup.zpowers_le.2 ⟨.of none, FreeGroup.lift_apply_of⟩)
  haveI : Countable (FreeGroup (Option (GL (Fin N) E))) := Quot.mk_surjective.countable
  exact ((Set.countable_range f).mono h).to_subtype

theorem left_latticeGL {φ : Sm E N} (h : IsAutForm φ) (h' : IsSqInt φ.1) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by
    intro x hx
    obtain ⟨γ, rfl⟩ := (show x ∈ (ratGL E N).range from hx)
    exact h.left γ) (Subgroup.zpowers_le.2 (h'.1 1))
  exact this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_of_isLocCompGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N),
    IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  intro E _ _ _ N V hV w σ ⟨f, h0, hf, hρ⟩
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
  haveI := countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  have hinj : Function.Injective f := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hρ, hv, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  refine isUnitarisable_of_embedding (Γ := latticeGL E N) σ.ρ (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp f) (Subtype.val_injective.comp hinj)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N (f v) (hV.aut _ (hf v)).level)
    (fun v => left_latticeGL (hV.aut _ (hf v)) (hV.sqInt _ (hf v))) (fun v => (hV.sqInt _ (hf v)).2)
    fun g v x => congrFun (congrArg Subtype.val (hρ g v)) x
  exact modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (cornerGL_transInv (sLoc E w) g)).trans (cornerGL_transInv (sFin E) _)) g

end GlobalTheory.DiscreteUnit
end

