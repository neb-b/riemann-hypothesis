module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0423
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.PrimesOverExistence.Places
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelAwayAdapted
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem apart_of_apart_not_apart {w w₀ u : HeightOneSpectrum (𝓞 E)} (hw : Apart w w₀) (hu : ¬ Apart u w₀) : Apart u w := by
  unfold Apart at *
  intro h
  exact hw (h.symm.trans (not_not.1 hu))

theorem mem_levelOf_iff_of_locU {w₀ w : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)}
    (hle : ∀ w, H w ≤ locU a w) (hfib : ∀ w u, ¬ Apart w u → H w = H u) (hw : Apart w w₀) {x : UA E a}
    (hx : x ∈ locU a w) : x ∈ levelOf a w₀ H ↔ x ∈ H w := by
  have hx' := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := (mem_levelOf.1 h).2.2 w hw
    rw [← eq_of_cLoc_eq (hle w hy) hx e]
    exact hy
  · intro h
    refine mem_levelOf.2 ⟨hx'.1, fun u hu => hx'.2 u (apart_of_apart_not_apart hw hu), fun w' hw' => ?_⟩
    by_cases hw'w : Apart w' w
    · exact ⟨1, one_mem _, by rw [map_one, hx'.2 w' hw'w]⟩
    · exact ⟨x, by rw [hfib w' w hw'w]; exact h, rfl⟩

theorem map_eq_image {w : HeightOneSpectrum (𝓞 E)} {L : Subgroup (UA E a)} (hL : L ≤ locU a w)
    (e : locU a w ≃ₜ* GL (Fin a) (w.adicCompletion E)) (he : ∀ x : locU a w, e x = cLoc w (x : UA E a)) :
    ((L.map (cLoc w) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) =
      e '' ((L.subgroupOf (locU a w) : Subgroup (locU a w)) : Set (locU a w)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hL hx⟩, Subgroup.mem_subgroupOf.2 hx, he _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, Subgroup.mem_subgroupOf.1 hy, (he y).symm⟩

theorem injective_of_compAlong {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (hirr : σ.IsIrreducible) (f : W →ₗ[ℂ] (UA E a → ℂ)) (hf0 : f ≠ 0)
    (hf : ∀ (x : locU a w) v, f (σ (((cLoc w).comp (locU a w).subtype) x) v) = RU E a x (f v)) :
    Function.Injective f := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  rw [← LinearMap.ker_eq_bot]
  refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr).2 _ (fun g u hu => ?_)).resolve_right fun h => hf0 ?_
  · rw [LinearMap.mem_ker] at hu ⊢
    have := hf (e.symm g) u
    have hg : ((cLoc w).comp (locU a w).subtype) (e.symm g) = g := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]
    rw [hg] at this
    rw [this, hu, map_zero]
  · refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this

theorem fix_of_fixed {U : Submodule ℂ (UA E a → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (hJ : GlobalTheory.PRep.fixed σ.ρ J ≠ ⊥) :
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ J → RU E a x φ = φ := by
  obtain ⟨hirr, f, hf0, hfU, hf⟩ := hc
  have hinj := injective_of_compAlong hw hirr f hf0 hf
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hJ
  refine ⟨f v, hfU v, fun h => hv0 (hinj (by rw [h, map_zero])), fun x hx hxJ => ?_⟩
  have := hf ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GlobalTheory.LGrp.mem_fixed.1 hv _ hxJ] at this
  exact this.symm

theorem fixed_ne_bot_of_fix {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {L : Subgroup (UA E a)} (hL : L ≤ locU a w) {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0)
    (hφ : ∀ x ∈ L, RU E a x φ = φ) : GlobalTheory.PRep.fixed σ.ρ (L.map (cLoc w)) ≠ ⊥ := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hp : (cLoc w).comp (locU a w).subtype = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  have hirr : Representation.IsIrreducible (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) := by
    rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  have hsup := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hc φ hφU
  let ι := {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}
  have hf' : ∀ (i : ι) (g : locU a w) (u : σ.V), i.1 ((σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) g u) =
      ((RU E a).comp (locU a w).subtype) g (i.1 u) := fun i g u => i.2.2 g u
  have hK : ∀ k ∈ {x : locU a w | (x : UA E a) ∈ L}, ((RU E a).comp (locU a w).subtype) k φ = (1 : ℂ) • φ :=
    fun k hk => by rw [one_smul]; exact hφ k.1 hk
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.SplitEigen.exists_eigen_of_mem_iSup (ι := ι) ((RU E a).comp (locU a w).subtype)
    (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) hirr (fun i => i.1) hf'
    {x : locU a w | (x : UA E a) ∈ L} (fun _ => 1) φ hφ0 hK hsup
  refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 ?_, hv0⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hv ⟨x, hL hx⟩ hx
  rw [one_smul] at this
  exact this

theorem KGL_le_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    GlobalTheory.LFun.KGL w (n := a) ≤ (intU a w).map (cLoc w) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  intro g hg
  have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
  exact ⟨(e.symm g).1, mem_intU_of (e.symm g).2 (by rw [h1]; exact hg), h1⟩

end GlobalTheory.Cong.AdaptLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupWeilElementCharacterKernelStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_weilElement_characterKernel : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) ∧ commutator (Dec (F := E) A) ≤ V ∧ (⟨(g : G E Ω), Weil_le_Dec h g.2⟩ : Dec (F := E) A) ∈ V ∧ ∀ t : Ine (F := E) A, ∀ x ∈ V, (x : G E Ω) = t → ∀ j, ξ j (a (ineIncl h t)) = 1 := by
  first | (exact @GlobalTheory.RoadU.exists_open_sub_charKer) | (exact GlobalTheory.RoadU.exists_open_sub_charKer) | (intros; apply GlobalTheory.RoadU.exists_open_sub_charKer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpan
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU.MuUnr

theorem exists_pow_eq_span {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)
open GlobalTheory.TwU.MuUnr

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section
namespace GlobalTheory.TwV.Xc.ClsPow

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_eq_diag_mul (y : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    ∃ (k : Eˣ) (u : (FiniteAdeleRing (𝓞 E) E)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = 1) ∧
      y ^ Fintype.card (ClassGroup (𝓞 E)) = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)).toMonoidHom k * u := by
  classical
  let a : Neutral.B1.Ideles E := ⟨((1 : InfiniteAdeleRing E), (y : FiniteAdeleRing (𝓞 E) E)),
    ((1 : InfiniteAdeleRing E), ((y⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)),
    Prod.ext (mul_one _) y.mul_inv, Prod.ext (mul_one _) y.inv_mul⟩
  have hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf E (a ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff E _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 E) E).2, ((u⁻¹ : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2, ?_, ?_⟩, fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((a ^ Fintype.card (ClassGroup (𝓞 E)) : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 =
        ((Neutral.B1.diagUnits E k * u : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 := by rw [he]
    have h3 : ∀ (t : Neutral.B1.Ideles E) (n : ℕ), ((t ^ n : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 = ((t : AdeleRing (𝓞 E) E).2) ^ n := by
      intro t n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl
    rw [h3] at h2
    rw [Units.val_pow_eq_pow_val]
    exact h2.trans rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_pow_eq_ratId_mul (x : (AfE F E)ˣ) :
    ∃ (a : Eˣ) (k : (AfE F E)ˣ), k ∈ intU F E ∧ x ^ Fintype.card (ClassGroup (𝓞 E)) = ratId F E a * k := by
  obtain ⟨ι, h1, h2⟩ := GlobalTheory.TwU.exists_isAdIso F E
  obtain ⟨a, u, hu, he⟩ := exists_pow_eq_diag_mul (Units.map ι.toRingHom.toMonoidHom x)
  have hinv : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) * ((u : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
      exact congrArg (fun t : FiniteAdeleRing (𝓞 E) E => t P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩
  · rw [intU, Submonoid.mem_units_iff]
    constructor
    · show ι.symm (u : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hu P]
    · show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hinv P]
  · apply Units.ext
    apply ι.injective
    have e := congrArg (fun t : (FiniteAdeleRing (𝓞 E) E)ˣ => (t : FiniteAdeleRing (𝓞 E) E)) he
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    rw [Units.val_pow_eq_pow_val, map_pow, e, Units.val_mul, map_mul]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    congr 1
    rw [ratId, Units.coe_map]
    show _ = ι (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (a : E))
    rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]

theorem conjId_ratId (σ : E →ₐ[F] E) (a : Eˣ) :
    conjId σ (ratId F E a) = ratId F E (Units.map (σ : E →+* E).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

theorem sigR_mem_RInt (σ : E →ₐ[F] E) {y : AfE F E} (hy : y ∈ RInt F E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ RInt F E := by
  have hle : RInt F E ≤ (RInt F E).comap (sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E b), ⟨RingOfIntegers.mapRingHom (σ : E →+* E) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨c, ?_⟩)
      simp [sigR]
  exact hle hy

theorem conjId_mem_intU (σ : E →ₐ[F] E) {k : (AfE F E)ˣ} (hk : k ∈ intU F E) : conjId σ k ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt σ hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt σ hk.2

theorem conjId_conjId (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (k : (AfE F E)ˣ) : conjId σ (conjId σ k) = k := by
  apply Units.ext
  show sigR σ (FiniteAdeleRing (𝓞 F) F) (sigR σ (FiniteAdeleRing (𝓞 F) F) (k : AfE F E)) = k
  induction (k : AfE F E) using TensorProduct.induction_on with
  | zero => simp
  | tmul e c => simp [sigR, hσ]
  | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht]

theorem normOne_idele_pow_eq_normOne_principal_mul_unit (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : (AfE F E)ˣ) (hx : x ∈ U1 σ) :
    ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧
      x ^ m = ratId F E z * k := by
  classical
  obtain ⟨a, k₀, hk₀, he⟩ := exists_pow_eq_ratId_mul (F := F) x
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hx' : x * conjId σ x = 1 := by
    rw [U1, MonoidHom.mem_ker] at hx
    exact hx
  have hw : x ^ h * conjId σ (x ^ h) = 1 := by rw [map_pow, ← mul_pow, hx', one_pow]
  have hw' : x ^ h = (conjId σ (x ^ h))⁻¹ := eq_inv_of_mul_eq_one_left hw
  let sa : Eˣ := Units.map (σ : E →+* E).toMonoidHom a
  refine ⟨2 * h, a * sa⁻¹, k₀ * (conjId σ k₀)⁻¹, Nat.mul_pos two_pos Fintype.card_pos, ?_, ?_, ?_, ?_⟩
  · have ha : (a : E) ≠ 0 := a.ne_zero
    have hsa : σ (a : E) ≠ 0 := by
      intro h0
      apply ha
      rw [← hσ (a : E), h0, map_zero]
    simp only [sa, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      AlgHom.coe_toRingHom, RingHom.coe_coe, map_mul, map_inv₀, hσ]
    field_simp
  · rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, map_inv, conjId_conjId σ hσ]
    rw [mul_assoc, inv_mul_cancel_left, mul_inv_cancel]
  · exact mul_mem hk₀ (inv_mem (conjId_mem_intU σ hk₀))
  · have hc : conjId σ (x ^ h) = ratId F E sa * conjId σ k₀ := by rw [he, map_mul, conjId_ratId]
    rw [mul_comm 2 h, pow_mul, sq]
    calc x ^ h * x ^ h = x ^ h * (conjId σ (x ^ h))⁻¹ := by rw [← hw']
      _ = ratId F E (a * sa⁻¹) * (k₀ * (conjId σ k₀)⁻¹) := by
        rw [hc, he, map_mul, map_inv, mul_inv]
        ac_rfl

theorem _root_.GlobalTheory.TwV.Xc.exists_pow_normOne_idele_eq_principal_mul_integralUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ x ∈ U1 σ, ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧ x ^ m = ratId F E z * k :=
  fun _ _ _ _ _ _ _ σ hσ x hx => normOne_idele_pow_eq_normOne_principal_mul_unit σ hσ x hx

end GlobalTheory.TwV.Xc.ClsPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveL.DecRes

variable {Ω F E : Type} [Field Ω] [Field F] [Field E] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
  (A : ValuationSubring Ω)

def lift (h : G F Ω) (hh : ∀ x : E, h (algebraMap E Ω x) = algebraMap E Ω x) : G E Ω :=
  { (h : Ω ≃+* Ω) with commutes' := hh }

def resHom : Dec (F := E) A →* Dec (F := F) A where
  toFun g := ⟨AlgEquiv.restrictScalarsHom F (g : G E Ω), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resHom_injective : Function.Injective (resHom (F := F) (E := E) A) := by
  intro g g' hgg
  apply Subtype.ext
  ext z
  have := congrArg (fun k : Dec (F := F) A => (k : G F Ω) z) hgg
  exact this

theorem mem_map_iff (V : Subgroup (Dec (F := E) A)) (g : Dec (F := E) A) :
    resHom (F := F) A g ∈ V.map (resHom (F := F) (E := E) A) ↔ g ∈ V :=
  (Subgroup.mem_map_iff_mem (resHom_injective (E := E) A))

variable (hfix : ∀ g ∈ Dec (F := F) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x)
include hfix

theorem resHom_surjective : Function.Surjective (resHom (F := F) (E := E) A) := by
  intro k
  exact ⟨⟨lift (k : G F Ω) (hfix _ k.2), k.2⟩, Subtype.ext (by ext z; rfl)⟩

theorem isOpen_map [FiniteDimensional F E] (V : Subgroup (Dec (F := E) A)) (hV : IsOpen (V : Set (Dec (F := E) A))) :
    IsOpen ((V.map (resHom (F := F) (E := E) A)) : Set (Dec (F := F) A)) := by
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have h1 : (1 : Dec (F := E) A) ∈ V := V.one_mem
  have hU1 : (1 : G E Ω) ∈ U := by
    have : (1 : Dec (F := E) A) ∈ Subtype.val ⁻¹' U := by rw [hUV]; exact h1
    exact this
  obtain ⟨K, hK, hKU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds hU1)
  haveI := hK
  haveI : FiniteDimensional F (K.restrictScalars F) :=
    (Module.Finite.trans E K : Module.Finite F K)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  have hO : IsOpen (Subtype.val ⁻¹' ((K.restrictScalars F).fixingSubgroup : Set (G F Ω)) : Set (Dec (F := F) A)) :=
    (IntermediateField.fixingSubgroup_isOpen (K.restrictScalars F)).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hO.mem_nhds ((K.restrictScalars F).fixingSubgroup.one_mem)) ?_
  intro k hk
  obtain ⟨g, rfl⟩ := resHom_surjective (E := E) A hfix k
  refine ⟨g, ?_, rfl⟩
  have hgU : (g : G E Ω) ∈ U := by
    apply hKU
    intro z
    exact hk ⟨z.1, z.2⟩
  have : g ∈ Subtype.val ⁻¹' U := hgU
  rw [hUV] at this
  exact this

theorem commutator_le_map (V : Subgroup (Dec (F := E) A)) (hc : commutator (Dec (F := E) A) ≤ V) :
    commutator (Dec (F := F) A) ≤ V.map (resHom (F := F) (E := E) A) := by
  have hs := resHom_surjective (E := E) A hfix
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator]
  exact Subgroup.map_mono (by rw [← commutator_def]; exact hc)

end GlobalTheory.AboveL.DecRes

namespace GlobalTheory.AboveL


open GlobalTheory.AboveL.DecRes in
theorem exists_cm_solvDisj_dec_eq : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ g ∈ Dec (F := maximalRealSubfield E) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) → ∀ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) → commutator (Dec (F := E) A) ≤ V → ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ ∀ g : Dec (F := E) A, (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ↔ g ∈ V := by
  intro Ω _ E _ _ _ _ _ A w h hfix V hVo hVc N hNo
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨n, hn, hnv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := E) A).mp ⟨w, h⟩
  obtain ⟨v, hv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := maximalRealSubfield E) A).mpr ⟨n, hn, hnv⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hNo
  obtain ⟨F₁, hfin, hab, hreal, hdecF, hsplit⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω (maximalRealSubfield E) A v hv
    (V.map (resHom (F := maximalRealSubfield E) (E := E) A)) (isOpen_map A hfix V hVo)
    (commutator_le_map A hfix V hVc) T hvT
  have hsolv : IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
    isSolvable_of_comm fun a b => hab.toIsMulCommutative.is_comm.comm a b
  obtain ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, hM, -⟩ :=
    hT F₁ hfin hab.toIsGalois hsolv hreal hsplit
  refine ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, fun g => ?_⟩
  rw [hM (g : G E Ω), ← mem_map_iff (F := maximalRealSubfield E) A V g, ← hdecF, IntermediateField.mem_fixingSubgroup_iff]
  rfl

end GlobalTheory.AboveL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPtMoveEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem isPt_move_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad), LocGood σ J A → LocInt A → LocHyp S A → A.ActB → (∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) → ∀ (i : G.comp) (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J → ∀ κa : S.U, A.IsAway i γ κa.1 → ∀ (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))), (∀ v, colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = colSpan (G.P.W v) (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) → ∀ x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κ.1 ∧ S.chi κ * S.chi κa = 1 := by
  intro F E _ _ _ _ _ σ n p G A J T f bad S hG hW hH hA hbad i γ hγ κa hκa g g' hg x x' hx hx'
  have hy := A.isPt_smul hA i g x.1 κa.1 hx γ hκa
  have hyU : GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κa.1⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (ratInU _ hγ) x.2) (Subgroup.inv_mem _ ((S.U_eq κa.1).1 κa.2).1)
  obtain ⟨κ₁, e₁, hχ₁⟩ := ptOne_of (A := A) S hW hH hbad i (fun v => colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (fun v => (G.lev i).act v γ * g v) g' ⟨_, hyU⟩ x' (fun v => rfl) (fun v => (hg v).symm) hy hx'
  refine ⟨κa⁻¹ * κ₁, ?_, ?_⟩
  · rw [e₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rw [map_mul, map_inv]
    apply Units.ext
    simp [hχ₁]

end GlobalTheory.TwV.Xc

end
end

