module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorAdjointDecaying
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.TrueGeo.SmallSec

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

theorem valAt_mul (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem regAt_pow {x : Z} (hf : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem valAt_pow (hf : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map (Scheme.stalkClosedPointTo y).hom).ne_zero

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = valR y U a := by
  have e : fnOf U h a = algebraMap _ Z.functionField (Z.presheaf.germ U (below y) hy a) :=
    (algebraMap_germ hy a).symm
  have ht : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y hy).ge
  have H := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  rw [e, valAt_algebraMap]
  first
  | rw [valR, dif_pos ht]
  | simp only [valR, dif_pos ht]
  | simp only [valR, ht, dite_true]
  refine H.trans ?_
  first
  | rfl
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; done)
  | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]; rfl)
  | (simp [Scheme.Hom.appLE]; done)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  rw [ratVal, dif_pos hf]
  have he := hf.exists_fnOf.choose_spec.choose_spec.choose_spec
  conv_rhs => rw [← he]
  exact (valAt_fnOf hf.exists_fnOf.choose_spec.choose _ _).symm

end Val

section Fn

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

def fnMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fnMap_fnOf {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) : fnMap j hη (fnOf U h s) = fnOf (j ⁻¹ᵁ U) h' (j.app U s) := by
  show (X.presheaf.germ U _ h ≫ X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom s =
    (j.app U ≫ Y.presheaf.germ (j ⁻¹ᵁ U) (genericPoint Y) h').hom s
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem fnMap_algebraMap_eq_algebraMap_stalkMap (y : Y) (b : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField b) = algebraMap _ Y.functionField (j.stalkMap y b) := by
  have e1 := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Y) y
    ((genericPoint_spec Y).specializes trivial) b
  simp only [RingHom.algebraMap_toAlgebra, fnMap]
  rw [← e1]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem exists_fnMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : RegAt y u) : ∃ t, RegAt (j y) t ∧ fnMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  exact ⟨algebraMap _ X.functionField b, ⟨b, rfl⟩, fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b⟩

theorem fnMap_surjective [IsPreimmersion j] : Function.Surjective (fnMap j hη) := fun u =>
  let ⟨t, _, ht⟩ := exists_fnMap_eq j hη (regAt_genericPoint u)
  ⟨t, ht⟩

theorem regAt_fnMap_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    RegAt y (fnMap j hη t) ↔ RegAt (j y) t := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fnMap_eq j hη h
    rwa [(fnMap j hη).injective e] at ht'
  · rintro ⟨b, rfl⟩
    exact ⟨_, (fnMap_algebraMap_eq_algebraMap_stalkMap j hη y b).symm⟩

theorem valAt_fnMap {K : Type} [Field K] (y : Sp K ⟶ Y) {t : X.functionField}
    (h : RegAt (j (below y)) t) : valAt y (fnMap j hη t) = valAt (y ≫ j) t := by
  obtain ⟨b, rfl⟩ := h
  rw [fnMap_algebraMap_eq_algebraMap_stalkMap, valAt_algebraMap]
  refine Eq.trans ?_ (valAt_algebraMap (y := y ≫ j) b).symm
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Fn

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)

theorem isPreimmersion_j : IsPreimmersion M.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip this

private theorem asIdeal_spMap_algebraMap_eq_bot (s : Sp F) : (spMap (algebraMap (𝓞 F) F) s).asIdeal = ⊥ := by
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  have e : (spMap (algebraMap (𝓞 F) F) s).asIdeal = Ideal.comap (algebraMap (𝓞 F) F) s.asIdeal := by
    first
    | rfl
    | simp [spMap]
    | simp [spMap, Spec.map_base]
  rw [e, hs]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j {x : M.X} (hx : (M.p x).asIdeal = ⊥) : x ∈ Set.range M.j := by
  have e : M.p x = spMap (algebraMap (𝓞 F) F) (IsLocalRing.closedPoint F) :=
    PrimeSpectrum.ext (hx.trans (asIdeal_spMap_algebraMap_eq_bot _).symm)
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ e
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz1, ← M.pb.isoPullback_inv_fst]
  first
  | rfl
  | exact (Scheme.comp_apply _ _ _).symm
  | simp

theorem asIdeal_p_j (y : Y.X) : (M.p (M.j y)).asIdeal = ⊥ := by
  have e : M.p (M.j y) = spMap (algebraMap (𝓞 F) F) (Y.str y) := by
    first
    | (show (M.j ≫ M.p) y = (Y.str ≫ spMap _) y
       rw [M.pb.w])
    | rw [← Scheme.comp_apply, M.pb.w, Scheme.comp_apply]
  rw [e, asIdeal_spMap_algebraMap_eq_bot]

theorem asIdeal_p_gen [IsIntegral M.X] : (M.p (genericPoint M.X)).asIdeal = ⊥ := by
  obtain ⟨y⟩ : Nonempty Y.X := inferInstance
  have hs : genericPoint M.X ⤳ M.j y := (genericPoint_spec M.X).specializes trivial
  have h3 : (M.p (genericPoint M.X)).asIdeal ≤ (M.p (M.j y)).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (M.p.base.hom.map_specializes hs)
  rw [asIdeal_p_j] at h3
  exact le_bot_iff.1 h3

theorem j_gen_specializes [IsIntegral M.X] : M.j (genericPoint Y.X) ⤳ genericPoint M.X := by
  obtain ⟨y0, hy0⟩ := mem_range_j M (asIdeal_p_gen M)
  rw [← hy0]
  exact M.j.base.hom.map_specializes ((genericPoint_spec Y.X).specializes trivial)

end Model

end GlobalTheory.TrueGeo.SmallSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0Three
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

end GlobalTheory.Mem.SJ.KernelJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftFin

variable {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
  {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)}

theorem word_ker (hκ : IsKerSys θ V W κ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (f : M) : ∃ f', ∀ h, word θ V l (fun g => κ f g h) = fun g => κ f' g h := by
  induction l with
  | nil => exact ⟨f, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨f'', e'⟩ := hκ.derV p.1 p.2 (hl p List.mem_cons_self) f'
    refine ⟨f'', fun h => ?_⟩
    change Rder θ V p.1 p.2 (word θ V l fun g => κ f g h) = _
    rw [e h]
    funext g
    exact (e' g h).deriv

theorem isMod_ker (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (f : M) (h : GA D W) : IsMod θ V fun g => κ f g h := by
  have hc : ∀ f, Continuous fun g => κ f g h := fun f => (hκ.cont f).comp (Continuous.prodMk_left h)
  refine ⟨_root_.GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V (Set.range fun f g => κ f g h) ?_ ?_ _ ⟨f, rfl⟩, fun γ hγ g => ?_, fun l hl => ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact hc f
  · rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hκ.derV τ X hX f
    exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
  · simpa using hκ.left f γ hγ 1 (one_mem _) g h
  · obtain ⟨f', e⟩ := word_ker hκ l hl f
    obtain ⟨N, hN⟩ := hκ.growth
    obtain ⟨C, hC⟩ := hN f'
    rw [e h]
    refine ⟨hc f', N, C * (height θ W h : ℝ) ^ N, fun g => (hC g h).trans_eq ?_⟩
    ring


variable (κ) in
def lift (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (f : M) (F : GA D V → ℂ) : GA D W → ℂ :=
  fun h => ∫ g in 𝓕, κ f g h * F g ∂μ

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem lift_add_left (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (f f' : M) : lift κ μ 𝓕 (f + f') F = lift κ μ 𝓕 f F + lift κ μ 𝓕 f' F := by
  have I := (_root_.GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1
  funext h
  simp only [lift, map_add (f := _), Pi.add_apply, add_mul]
  exact integral_add (I f h) (I f' h)

theorem lift_add_right (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F F' : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (hF' : F' ∈ Decay θ V) (f : M) :
    lift κ μ 𝓕 f (F + F') = lift κ μ 𝓕 f F + lift κ μ 𝓕 f F' := by
  funext h
  simp only [lift, Pi.add_apply, mul_add]
  exact integral_add ((_root_.GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1 f h)
    ((_root_.GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F' hF').1 f h)

theorem lift_smul_left (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 (c • f) F = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem lift_smul_right (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 f (c • F) = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _


variable (θ κ μ 𝓕) in
def Compat (T : (GA D W → ℂ) → (GA D W → ℂ)) : Prop :=
  ∀ f, ∃ f', (∀ g, T (κ f g) = κ f' g) ∧ ∀ F ∈ Decay θ V, T (lift κ μ 𝓕 f F) = lift κ μ 𝓕 f' F

theorem compat_id : Compat θ κ μ 𝓕 fun φ => φ := fun f => ⟨f, fun _ => rfl, fun _ _ => rfl⟩

theorem Compat.comp {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S (T φ) := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  obtain ⟨f'', c, d⟩ := hS f'
  exact ⟨f'', fun g => by simp only [a, c], fun F hF => by simp only [b F hF, d F hF]⟩

theorem Compat.add (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕)
    {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S φ + T φ := fun f => by
  obtain ⟨f', a, b⟩ := hS f
  obtain ⟨f'', c, d⟩ := hT f
  exact ⟨f' + f'', fun g => by simp only [a, c, map_add (f := _), Pi.add_apply],
    fun F hF => by simp only [b F hF, d F hF, lift_add_left hθ hκ hq hF]⟩

theorem Compat.smul (c : ℂ) {T : (GA D W → ℂ) → (GA D W → ℂ)} (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => c • T φ := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  exact ⟨c • f', fun g => by simp only [a, map_smul, Pi.smul_apply], fun F hF => by simp only [b F hF, lift_smul_left]⟩

theorem compat_sum (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {ι : Type} (s : Finset ι)
    (T : ι → (GA D W → ℂ) → (GA D W → ℂ)) (hT : ∀ i, Compat θ κ μ 𝓕 (T i)) :
    Compat θ κ μ 𝓕 fun φ => ∑ i ∈ s, T i φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (compat_id (θ := θ) (κ := κ) (μ := μ) (𝓕 := 𝓕)).smul 0
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (hT i).add hθ hκ hq ih

theorem compat_foldr (l : List ((GA D W → ℂ) → (GA D W → ℂ))) (hl : ∀ T ∈ l, Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => l.foldr (fun T acc => T acc) φ := by
  induction l with
  | nil => exact compat_id
  | cons T l ih => exact (hl T List.mem_cons_self).comp (ih fun S hS => hl S (List.mem_cons_of_mem _ hS))

theorem compat_Rder (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {X : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hX : X ∈ lieAt W τ) : Compat θ κ μ 𝓕 (Rder θ W τ X) := fun f => by
  obtain ⟨f', e⟩ := hκ.derW τ X hX f
  exact ⟨f', fun g => funext fun h => (e g h).deriv, fun F hF => funext fun h =>
    ((_root_.GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).2.2.2 τ X hX f f' e h).deriv⟩

theorem compat_gelf (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) (τ : D.what₂.Tau) (k : ℕ) :
    Compat θ κ μ 𝓕 (gelf θ W τ k) := by
  refine compat_sum hθ hκ hq Finset.univ _ fun idx : Fin (k + 1) → Fin W.rank =>
    compat_foldr (List.ofFn fun a : Fin (k + 1) => RderC θ W τ (Matrix.single (idx a) (idx (a + 1)) 1)) fun T hT => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem W τ (Matrix.single (idx a) (idx (a + 1)) 1)
  exact (compat_Rder hθ hκ hq h1).add hθ hκ hq ((compat_Rder hθ hκ hq h2).smul Complex.I)

theorem lift_adjoin (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {a : ℕ → Module.End ℂ M} (ha : ∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h)
    {Z : Submodule ℂ (GA D V → ℂ)} (hZ : ∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) {x : Module.End ℂ M}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ f, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, lift κ μ 𝓕 (x f) F = lift κ μ 𝓕 f F' := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro f F hF
    obtain ⟨F', hF', e⟩ := _root_.GlobalTheory.Mem.GelfParts.gelf_by_parts D θ hθ V μ 𝓕 hq τ Z hZ k F hF
    refine ⟨F', hF', funext fun h => ?_⟩
    have := e _ (isMod_ker hθ hκ f h)
    rw [ha] at this
    exact this
  | algebraMap r =>
    intro f F hF
    exact ⟨r • F, Submodule.smul_mem _ r hF, by rw [Module.algebraMap_end_apply, lift_smul_left, lift_smul_right]⟩
  | add x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx f F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F hF
    exact ⟨F₁ + F₂, add_mem h₁ h₂, by
      rw [LinearMap.add_apply, lift_add_left hθ hκ hq hF.1, lift_add_right hθ hκ hq h₁.1 h₂.1, e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx (y f) F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F₁ h₁
    exact ⟨F₂, h₂, by rw [Module.End.mul_apply, e₁, e₂]⟩

theorem lift_zfin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  rintro D θ hθ V W M _ _ κ hκ μ 𝓕 hq F hF ⟨Z, hfin, hFZ, hZ⟩ f
  let L : ↥(Decay θ V ⊓ Z) →ₗ[ℂ] (GA D W → ℂ) :=
    { toFun := fun F' => lift κ μ 𝓕 f F'.1
      map_add' := fun F₁ F₂ => lift_add_right hθ hκ hq F₁.2.1 F₂.2.1 f
      map_smul' := fun c F' => lift_smul_right c F'.1 f }
  refine ⟨LinearMap.range L, inferInstance, ⟨⟨F, hF, hFZ⟩, rfl⟩, ?_⟩
  rintro τ k _ ⟨F₁, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hκ.cap τ
  obtain ⟨f', e, e'⟩ := compat_gelf hθ hκ hq τ k f
  obtain ⟨F₂, h₂, e₂⟩ := lift_adjoin hθ hκ hq ha (hZ τ) (hab ▸ Algebra.subset_adjoin ⟨k, rfl⟩ : b k ∈ _) f F₁.1 F₁.2
  refine ⟨⟨F₂, h₂⟩, ?_⟩
  change lift κ μ 𝓕 f F₂ = gelf θ W τ k (lift κ μ 𝓕 f F₁.1)
  rw [e' _ F₁.2.1, ← e₂]
  funext h
  simp only [lift, ← e, hb]

end GlobalTheory.Mem.LiftFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem lvlE_range_iff : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  have h := congrArg (fun s : Set S.Forms => f ∈ s) (GlobalTheory.Mem.LiftForms.range_lvlForm S r P ψ)
  simp only [Set.mem_range, GlobalTheory.Mem.LiftForms.lvlForm_apply] at h
  rw [h]
  rfl

end GlobalTheory.TopSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeRestrictionInjectiveOnMultiplicity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LowRes

theorem multW_lowRes_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), ∀ w ∈ (y.L F.lv2).MultW i, w ∘ₗ (y.L F.lv2).embK i = 0 → w = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP _ y i w hw hK
  have hM := hP.char.base.models
  set M := R.MW i (sg0 D A3.A)
  let w' : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap M := PiTensorProduct.lift.symm w'
  have hU : U ∈ Mult R.θ M _ _ := (Mult.mem_multT _ _ _ _ w').1 hw
  have h0 : U = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ M R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
        have e := LinearMap.congr_fun hK (PiTensorProduct.tprod ℂ v)
        have e2 : w' (PiTensorProduct.map (fun τ => (lowT M τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
        rw [PiTensorProduct.map_tprod] at e2
        have e3 : PiTensorProduct.lift U (PiTensorProduct.tprod ℂ (fun τ => (lowT M τ).subtype (v τ))) = 0 := by
          rw [show PiTensorProduct.lift U = w' from LinearEquiv.apply_symm_apply _ w']; exact e2
        rw [PiTensorProduct.lift.tprod] at e3
        exact e3)
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  show w' = 0
  rw [← hUw, h0, map_zero]

end GlobalTheory.Mem.R3.Rw.LowRes

end
end

