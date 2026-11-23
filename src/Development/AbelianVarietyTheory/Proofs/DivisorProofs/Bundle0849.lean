module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatBound

variable {E : Type} [Field E] [NumberField E]

theorem coord_mul (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem coord_add (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z + z') w = z w + z' w := rfl

theorem integral_of_int (b : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (algebraMap (𝓞 E) E b)) w ∈ w.adicCompletionIntegers E :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
    ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le (w.valuation_le_one b))

theorem integral_natCast (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ((n : Af E)) w ∈ w.adicCompletionIntegers E := by
  have := integral_of_int (E := E) (n : 𝓞 E) w
  simpa using this

theorem exists_nat_mul_integral (z : Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((d : Af E) * z) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨x, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z
  obtain ⟨m, hm0, hm⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))
  have hint : IsIntegral ℤ ((m.natAbs : E) * x) := by
    rcases Int.natAbs_eq m with h1 | h1
    · have : ((m.natAbs : E) * x) = m • x := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, ← h1]
      rw [this]; exact hm
    · have h1' : (m.natAbs : ℤ) = -m := by omega
      have : ((m.natAbs : E) * x) = -(m • x) := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, h1', Int.cast_neg, neg_mul]
      rw [this]; exact hm.neg
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun w => ?_⟩
  have e : (m.natAbs : Af E) * z =
      algebraMap E (Af E) (algebraMap (𝓞 E) E ⟨_, hint⟩) + (m.natAbs : Af E) * a := by
    rw [h, one_smul, mul_add]
    congr 1
    show _ = algebraMap E (Af E) ((m.natAbs : E) * x)
    rw [map_mul, map_natCast]
  rw [e, coord_add, coord_mul]
  exact add_mem (integral_of_int _ w) (mul_mem (integral_natCast _ w) (ha w))

theorem integral_of_mem_hatO [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : z ∈ hatO c)
    (w : HeightOneSpectrum (𝓞 E)) : z w ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, -, ha, hza⟩ := (GlobalTheory.CMVal.HatPlace.mem_hatO_iff E c hc z).1 hz
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : Valued.v (z w - a w) ≤ 1 :=
    (hza w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have h2 : z w = (z w - a w) + a w := by ring
  rw [h2]
  exact Valuation.map_add_le _ h1 (ha w)

theorem lattice_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ lattice c y) ∧
      ∀ x ∈ lattice c y, IsIntegral ℤ ((N : E) * x) := by
  intro E _ _ _ c hc y
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_integral (y : Af E)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_integral (↑y⁻¹ : Af E)
  have hN₁ : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨Ideal.absNorm c * d₁ * d₂, by positivity, fun x => ?_, fun x hx => ?_⟩
  · rw [mem_lattice]
    have hY : ∀ w : HeightOneSpectrum (𝓞 E),
        (algebraMap E (Af E) (algebraMap (𝓞 E) E x) * (d₁ : Af E) * ((d₂ : Af E) * (↑y⁻¹ : Af E))) w ∈
          w.adicCompletionIntegers E := fun w => by
      rw [coord_mul, coord_mul]
      exact mul_mem (mul_mem (integral_of_int x w) (integral_natCast d₁ w)) (h₂ w)
    have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hY
    convert key using 1
    rw [map_natCast, map_natCast, map_mul, map_natCast]
    push_cast
    ring
  · rw [mem_lattice] at hx
    have hz := integral_of_mem_hatO hc hx
    have hint : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E ((d₁ : E) * x) ≤ 1 := fun w => by
      have e : algebraMap E (Af E) ((d₁ : E) * x) =
          (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * ((d₁ : Af E) * (y : Af E)) := by
        rw [map_mul, map_natCast]
        have : (↑y⁻¹ : Af E) * (y : Af E) = 1 := Units.inv_mul y
        linear_combination (-(d₁ : Af E) * algebraMap E (Af E) x) * this
      have h3 : (algebraMap E (Af E) ((d₁ : E) * x)) w ∈ w.adicCompletionIntegers E := by
        rw [e, coord_mul]; exact mul_mem (hz w) (h₁ w)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h3
      exact h3
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ hint
    have e2 : ((Ideal.absNorm c * d₁ * d₂ : ℕ) : E) * x =
        algebraMap (𝓞 E) E (((Ideal.absNorm c * d₂ : ℕ) : 𝓞 E) * b) := by
      rw [map_mul, hb, map_natCast]; push_cast; ring
    rw [e2]
    exact RingOfIntegers.isIntegral_coe _

end GlobalTheory.CMVal.LatBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfLevelLift
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HTLift

open GlobalTheory.SiegelPull

theorem push_comp' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A}
    (hab : α.left ≫ φ = φ ≫ β.left) (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

theorem exists_obj_of_isLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S)
    (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s))
    (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  intro p _ D R _ b N N' hd hc S s o T lv hL
  obtain ⟨hadd, hker, hlin, hlev, hgeom⟩ := hL
  obtain ⟨oT, ⟨mT⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N S T.left s T.hom o
  have pb := mT.cart
  let eta : D.La → (𝟙_ (Over T.left) ⟶ oT.A) := fun a =>
    Over.homMk (pb.1.lift (lv a).left (𝟙 _) (by rw [Over.w, Category.id_comp])) (pb.1.lift_snd _ _ _)
  have etaφ : ∀ a, (eta a).left ≫ mT.φ = (lv a).left := fun a => pb.1.lift_fst _ _ _
  let u : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, pushHom pb _ (eta a) = u ≫ lv a := fun a => Over.OverMorphism.ext (by
    show (eta a).left ≫ mT.φ = 𝟙 T.left ≫ (lv a).left
    rw [Category.id_comp]; exact etaφ a)
  let o'' : Obj b N' (T.hom ≫ s) :=
    { A := oT.A
      ab := oT.ab
      act := oT.act
      P := oT.P
      isLB := oT.isLB
      rig₁ := oT.rig₁
      rig₂ := oT.rig₂
      symm := oT.symm
      ample := oT.ample
      kerP := oT.kerP
      rosati := oT.rosati
      lie := oT.lie
      lieRank := oT.lieRank
      eta := eta
      eta_add := fun y z => push_injective pb _ (by
        rw [map_mul, key, key, key, hadd, MonObj.comp_mul])
      eta_lin := fun c y => push_injective pb _ (by
        rw [push_comp' pb (mT.act c), key, key, hlin, Category.assoc])
      eta_ker := fun y => push_injective pb _ (by
        rw [key, hker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := hgeom k x
        let e : (Over.mk x ⟶ oT.A) ≃* (Over.mk (x ≫ T.hom) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨push_injective pb _, push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ oT.act.act c) = e g ≫ o.act.act c := fun c g => push_comp' pb (mT.act c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ mT.φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        have dg := diag_iso mT.sq mT.pol
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S T.left o.A oT.A T.hom mT.φ _ _
                    (pull_isLB o.isLB _) (pull_isLB oT.isLB _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _
                    (ex _) (ex _)).2 (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ eta y = e.symm (I.ev N' y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        apply Over.OverMorphism.ext
        show x ≫ (lv y).left = ((toUnit (Over.mk x)).left ≫ (eta y).left) ≫ mT.φ
        rw [Category.assoc, etaφ, Over.toUnit_left]
        rfl }
  let mm : ObjMap (o''.forget N hd hc) o T.hom :=
    { φ := mT.φ, φ₂ := mT.φ₂, cart := mT.cart, sq := mT.sq, act := mT.act, pol := mT.pol,
      eta := fun y => by
        show (eta ((N' / N) • y)).left ≫ mT.φ = T.hom ≫ (o.eta y).left
        rw [etaφ, hlev, Over.comp_left, Over.toUnit_left] }
  exact ⟨o'', mm, fun a => etaφ a⟩

end GlobalTheory.HTLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMeanSquareForm

open GlobalTheory.HeisOrtho

theorem exists_form {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (M : Submodule ℂ (X → ℂ))
    (hm : ∀ f ∈ M, Measurable f) (hb : ∀ f ∈ M, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ f g : M, B f g = ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ∧
      ∀ f : M, ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (B f f).re := by
  have hi : ∀ f g : M, Integrable (fun x => (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x)) ν := fun f g => by
    obtain ⟨C, hC⟩ := hb f f.2
    obtain ⟨C', hC'⟩ := hb g g.2
    refine Integrable.of_bound
      (((hm f f.2).mul (Complex.continuous_conj.measurable.comp (hm g g.2))).aestronglyMeasurable)
      (C * C') (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f g : M => ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ?_ ?_ ?_ ?_, fun _ _ => rfl, fun f => ?_⟩
  · intro f f' g
    rw [← integral_add (hi f g) (hi f' g)]
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  · intro c f g
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · intro f g g'
    rw [← integral_add (hi f g) (hi f g')]
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]
  · intro c f g
    rw [smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]
  · rw [LinearMap.mk₂'ₛₗ_apply]
    have h1 : Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) ν := by
      refine (hi f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, Complex.ofReal_re,
      ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  intro D ψ S T hψ M hM μ 𝓕 hμ h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨B, hB, hN⟩ := exists_form (μ.restrict 𝓕) M (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨B, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hB, hB, hf, hg]
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun w => (f : WO S T → ℂ) w * (starRingEnd ℂ) ((g : WO S T → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T (ratW T S γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WO S T → ℂ) (ratW T S γ + w) * (starRingEnd ℂ) ((g : WO S T → ℂ) (ratW T S γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w u))
  show ψ (symplOH S T w u) * (f : WO S T → ℂ) (w + u) *
    (starRingEnd ℂ) (ψ (symplOH S T w u) * (g : WO S T → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeAutomorphismModHalfLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInduce

section Abstract

variable {R L A : Type} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup A]

theorem exists_induced (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C) :
    ∃ f : (L ⧸ N) →ₗ[R] (L ⧸ N), ∀ a b, f (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  choose g hg using fun a => hon (k (φ a)) (hkH _ (hφ a))
  have key : ∀ a b, N.mkQ (g a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hN, map_sub]
    constructor
    · intro h
      have := add_mem (hg a) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hg a)
      rwa [sub_sub_sub_cancel_left] at this
  let g0 : L →ₗ[R] (L ⧸ N) :=
    { toFun := fun a => N.mkQ (g a)
      map_add' := fun a b => by
        rw [← map_add (f := _), key, map_add (f := _), map_add (f := _), map_add (f := _), add_sub_add_comm]
        exact add_mem (hg a) (hg b)
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← map_smul, key, hφs, hφs, hks, ← map_sub]
        exact hs r _ (hg a) }
  refine ⟨N.liftQ g0 fun a ha => ?_, fun a b => key a b⟩
  change N.mkQ (g a) = 0
  rw [← map_zero N.mkQ, key, map_zero, sub_zero]
  exact hkC _ ((hN a).2 ha)

theorem exists_induced_equiv (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C)
    (k' : A →+ A) (hks' : ∀ r z, k' (s r z) = s r (k' z)) (hkH' : ∀ z ∈ H, k' z ∈ H) (hkC' : ∀ z ∈ C, k' z ∈ C)
    (h1 : ∀ z, k (k' z) = z) (h2 : ∀ z, k' (k z) = z) :
    ∃ γ : (L ⧸ N) ≃ₗ[R] (L ⧸ N), ∀ a b, γ (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  obtain ⟨f, hf⟩ := exists_induced N φ s H C hφs hs hφ hN hon k hks hkH hkC
  obtain ⟨f', hf'⟩ := exists_induced N φ s H C hφs hs hφ hN hon k' hks' hkH' hkC'
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, hf⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f' (N.mkQ a))
    have h := neg_mem (hkC _ ((hf' a b).1 hb.symm))
    rw [map_sub, h1, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf b a).2 h
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f (N.mkQ a))
    have h := neg_mem (hkC' _ ((hf a b).1 hb.symm))
    rw [map_sub, h2, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf' b a).2 h

end Abstract

section Space

variable {D : D7} (V : HSp D)

noncomputable def halfHom (b : 𝓞 D.host.E) :
    (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.mk' (halfVec V b) fun _ _ => funext fun _ => mul_add _ _ _

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

theorem mulVec_halfVec (m : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) : m *ᵥ halfVec V b z = halfVec V b (m *ᵥ z) := by
  rw [halfVec_eq, halfVec_eq, Matrix.mulVec_smul]

theorem map_closure_mem (I : Ideal (𝓞 D.host.E))
    (k : (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))
    (hks : ∀ r z, k (halfVec V r z) = halfVec V r (k z)) (hk : ∀ z ∈ latGHat V 1, k z ∈ latGHat V 1) :
    ∀ z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z},
      k z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, k z, hk z hz, hks b z⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end Space

theorem exists_levGrp_induced : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro D V H Dw l ι hι κ hκ
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMmem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have h : (l.M : 𝓞 D.host.E) ∈ Ideal.span {(l.M : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hMb : l.Mb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hMmem
    exact hM0.ne' (Nat.cast_eq_zero.1 hMmem)
  have hκ1 : ∀ z ∈ latGHat V 1, (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ.2
  have hκ0 : ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hκ.2 z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  have hκ2 : ∀ z ∈ latGHat V 1, (finHom V κ⁻¹).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ⁻¹).1.2 fun z hz =>
      ⟨_, sub_mem (GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ hκ0 z hz) hz, (one_smul _ _).symm⟩
  let φ : Dw.La →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun a => finVec V (ι a)) fun a b => by
      rw [map_add (f := _)]
      exact GlobalTheory.Member.AALev.fv_add _ _
  have hmem : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have hsH : ∀ r, ∀ z ∈ latGHat V 1, halfHom V r z ∈ latGHat V 1 := by
    intro r z hz
    rw [hhat] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int (latG V 1) r hz
  obtain ⟨γ, hγ⟩ := exists_induced_equiv (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) φ (halfHom V) (latGHat V 1)
    (AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z})
    (fun r a => by
      change finVec V (ι (r • a)) = _
      rw [map_smul]
      exact GlobalTheory.Member.AALev.fv_smul (r : D.host.E) (ι a))
    (fun r => map_closure_mem V l.Mb (halfHom V r) (fun _ _ => funext fun _ => mul_left_comm _ _ _) (hsH r))
    (fun a => by
      rw [hhat]
      exact GlobalTheory.Member.AALev.fv_mem_hat _ (hmem a))
    (fun a => by
      refine (_root_.GlobalTheory.IdealCap.finVec_mem_closure_iff D V l.Mb hMb (ι a)).trans ?_
      rw [← hι.2, LinearMap.range_eq_map, ← Submodule.map_smul'']
      constructor
      · rintro ⟨x, hx, e⟩
        exact hι.1 e ▸ hx
      · exact fun h => ⟨a, h, rfl⟩)
    (fun z hz => by
      rw [hhat] at hz
      obtain ⟨x, hx, w, hw, e⟩ :=
        (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ hfg hsp).2.1 l.M hM0 z hz
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← hhat] at hw
      refine ⟨a, AddSubgroup.subset_closure ⟨_, hMmem, w, hw, ?_⟩⟩
      rw [e]
      refine (add_sub_cancel_left _ _).trans ?_
      rw [halfVec_eq, ← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E)]
      congr 1
      exact (map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) l.M).symm)
    (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom (mulVec_halfVec V _) hκ1
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ1)
    (Matrix.mulVecLin (finHom V κ⁻¹).1).toAddMonoidHom (mulVec_halfVec V _) hκ2
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ2)
    (fun z => by
      change (finHom V κ).1 *ᵥ ((finHom V κ⁻¹).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec])
    (fun z => by
      change (finHom V κ⁻¹).1 *ᵥ ((finHom V κ).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec])
  exact ⟨γ, fun a => (hγ a _).1 (liftLa_spec γ a).symm⟩

end GlobalTheory.StabInduce
end

