module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingFw
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2SurjectiveUniverses
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegersStatement
section
open NumberField GlobalTheory.UPel.HT
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_La_ringOfIntegers' :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  let : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have h : Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
    let : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
    have : IsScalarTower (𝓞 D.F) D.F D.VF :=
      ⟨fun c x v => by
        show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
        rw [mul_smul]⟩
    let f : D.La →ₗ[𝓞 D.F] D.VF :=
      { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
        map_add' := fun z w => TensorProduct.tmul_add _ _ _
        map_smul' := fun c z => by
          rw [RingHom.id_apply]
          show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
            algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
          rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
          rfl }
    have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

    have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
      intro n v
      show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
      rw [map_natCast, Nat.cast_smul_eq_nsmul]
    have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
      constructor
      · rintro ⟨c, hc⟩
        have hc0 : (c : D.F) ≠ 0 := by
          intro h
          exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
        rw [Module.End.isUnit_iff]
        constructor
        · intro v w h
          have h' : (c : D.F) • v = (c : D.F) • w := h
          exact smul_right_injective D.VF hc0 h'
        · intro v
          refine ⟨(c : D.F)⁻¹ • v, ?_⟩
          show (c : D.F) • ((c : D.F)⁻¹ • v) = v
          rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      · intro y
        obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
        have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
          mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
        refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
        show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
        rw [hnat, hf, hy]
        show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
        rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
          zsmul_eq_mul, mul_one]
      · intro z w h
        rw [hf, hf] at h
        obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
          (TensorProduct.mk ℤ ℚ D.La 1)).1 h
        have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
          exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
        refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
        show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
        rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact hcz
    have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
    have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
    rw [← h1, ← h2, D.finrank_VF]
  exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexRestrictionBijectiveCollapse
section
open CategoryTheory GlobalTheory.CxCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CxCoh.Collapse

theorem bij_of_two {A B X Y : Type*} (r : A → B) (w : B → X) (s : X → Y) (U : A → X) (E : B → Y)
    (hU : ∀ x, U x = w (r x)) (hE : ∀ y, E y = s (w y))
    (bU : Function.Bijective U) (bE : Function.Bijective E) : Function.Bijective r := by
  have wi : Function.Injective w := fun y y' h ↦ bE.1 (by rw [hE, hE, h])
  refine ⟨fun x x' h ↦ bU.1 (by rw [hU, hU, h]), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := bU.2 (w y)
  exact ⟨x, wi (by rw [← hU, hx])⟩

variable {C : Type 1} [Category.{0} C] {D : Type} [Category.{0} D]

def uMap (K : Cx C) (S : C ⥤ C) (u : 𝟭 C ⟶ S) : CxMap K (K.res S) where
  G := 𝟭 C
  a0 T := K.M0.map (u.app T)
  a1 T := K.M1.map (u.app T)
  a2 T := K.M2.map (u.app T)
  a3 T := K.M3.map (u.app T)
  compDegreeZero_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M0.map_comp, ← K.M0.map_comp, h]
  compDegreeOne_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M1.map_comp, ← K.M1.map_comp, h]
  compDegreeTwo_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M2.map_comp, ← K.M2.map_comp, h]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

def wMap (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (w : q ⋙ ℓ ⟶ S) : CxMap (K.res ℓ) (K.res S) where
  G := q
  a0 T := K.M0.map (w.app T)
  a1 T := K.M1.map (w.app T)
  a2 T := K.M2.map (w.app T)
  a3 T := K.M3.map (w.app T)
  compDegreeZero_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M0.map (w.app T') (K.M0.map (ℓ.map (q.map φ)) x) = K.M0.map (S.map φ) (K.M0.map (w.app T) x)
    rw [← K.M0.map_comp, ← K.M0.map_comp, this]
  compDegreeOne_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M1.map (w.app T') (K.M1.map (ℓ.map (q.map φ)) x) = K.M1.map (S.map φ) (K.M1.map (w.app T) x)
    rw [← K.M1.map_comp, ← K.M1.map_comp, this]
  compDegreeTwo_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M2.map (w.app T') (K.M2.map (ℓ.map (q.map φ)) x) = K.M2.map (S.map φ) (K.M2.map (w.app T) x)
    rw [← K.M2.map_comp, ← K.M2.map_comp, this]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

def eMap (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q) :
    CxMap (K.res ℓ) ((K.res S).res ℓ) where
  G := 𝟭 D
  a0 T := K.M0.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a1 T := K.M1.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a2 T := K.M2.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a3 T := K.M3.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  compDegreeZero_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M0.map _ (K.M0.map (ℓ.map φ) x) = K.M0.map (S.map (ℓ.map φ)) (K.M0.map _ x)
    rw [← K.M0.map_comp, ← K.M0.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  compDegreeOne_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M1.map _ (K.M1.map (ℓ.map φ) x) = K.M1.map (S.map (ℓ.map φ)) (K.M1.map _ x)
    rw [← K.M1.map_comp, ← K.M1.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  compDegreeTwo_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M2.map _ (K.M2.map (ℓ.map φ) x) = K.M2.map (S.map (ℓ.map φ)) (K.M2.map _ x)
    rw [← K.M2.map_comp, ← K.M2.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

end GlobalTheory.CxCoh.Collapse


open GlobalTheory.CxCoh.Collapse in
theorem GlobalTheory.CxCoh.collapse_resMap_bij : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (ℓ : D ⥤ C)
    (q : C ⥤ D) (S : C ⥤ C) (u : 𝟭 C ⟶ S) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q), (∀ T, K.QAt (u.app T)) →
    (∀ U, K.QAt (ℓ.map (ε.app U) ≫ w.app (ℓ.obj U))) → (K.resMap ℓ).Bij := by
  intro C _ D _ K ℓ q S u w ε hu hε
  let U := uMap K S u
  let W := wMap K ℓ q S w
  let E := eMap K ℓ q S w ε
  have jU : U.Joined (K.resMap S) u := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have jW : ((K.resMap ℓ).comp W).Joined (K.resMap S) w := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have jE : E.Joined (W.comp ((K.res S).resMap ℓ)) ε :=
    ⟨fun _ x ↦ (K.M0.map_comp _ _ x).symm, fun _ x ↦ (K.M1.map_comp _ _ x).symm,
      fun _ x ↦ (K.M2.map_comp _ _ x).symm⟩
  have qU : U.QAll := hu
  have qE : E.QAll := hε
  have a0U := _root_.GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1.1 U qU
  have a1U := _root_.GlobalTheory.CxCoh.VertSurj.instances.1 U qU
  have a2U := _root_.GlobalTheory.CxCoh.vertical_h2_injective_universes.1 U qU
  have a3U := _root_.GlobalTheory.CxCoh.VertSurjTwo.inst.1 U qU
  have a0E := _root_.GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1.2.2 E qE
  have a1E := _root_.GlobalTheory.CxCoh.VertSurj.instances.2.2 E qE
  have a2E := _root_.GlobalTheory.CxCoh.vertical_h2_injective_universes.2.2 E qE
  have a3E := _root_.GlobalTheory.CxCoh.VertSurjTwo.inst.2.2 E qE
  have oU := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.1 _ _ _ jU
  have oW := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.1 _ _ _ jW
  have oE := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.2.2 _ _ _ jE
  have tU := _root_.GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst.1 _ _ _ jU
  have tW := _root_.GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst.1 _ _ _ jW
  have tE := _root_.GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst.2.2 _ _ _ jE
  refine ⟨bij_of_two _ W.h0 ((K.res S).resMap ℓ).h0 U.h0 E.h0 (fun x ↦ ?_) (fun y ↦ ?_) a0U.1 a0E.1,
    bij_of_two _ W.h1 ((K.res S).resMap ℓ).h1 U.h1 E.h1 (fun x ↦ ?_) (fun y ↦ ?_) ⟨a0U.2, a1U⟩ ⟨a0E.2, a1E⟩,
    bij_of_two _ W.h2 ((K.res S).resMap ℓ).h2 U.h2 E.h2 (fun x ↦ ?_) (fun y ↦ ?_) ⟨a2U, a3U⟩ ⟨a2E, a3E⟩⟩
  · rw [oU.1, ← oW.1, CxMap.cohomZero_pullback_comp]
  · rw [oE.1, CxMap.cohomZero_pullback_comp]
  · rw [oU.2, ← oW.2, CxMap.cohomOne_pullback_comp]
  · rw [oE.2, CxMap.cohomOne_pullback_comp]
  · rw [tU, ← tW, CxMap.cohomTwo_pullback_comp]
  · rw [tE, CxMap.cohomTwo_pullback_comp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInv
section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.DiscClass

theorem G_eq_of_mul (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) (k : ℕ) :
    Λ.G k = u ^ k * Λ'.G k := by
  let e : (Λ.lattice : Set ℂ) ≃ (Λ'.lattice : Set ℂ) :=
    (Equiv.mulLeft₀ u hu).subtypeEquiv fun w => by simpa using (h w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : (Λ'.lattice : Set ℂ)) : ℂ) = u * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]

theorem latDisc_eq_of_mul (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) :
    latDisc Λ = u ^ 12 * latDisc Λ' := by
  simp only [latDisc, PeriodPair.g₂, PeriodPair.g₃, G_eq_of_mul Λ Λ' u hu h 4, G_eq_of_mul Λ Λ' u hu h 6]
  ring

theorem abs_norm_eq_norm_sq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (x : K) :
    ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ‖φK x‖ ^ 2 := by
  have hcx : (InfinitePlace.mk φK).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff]
    intro e
    apply hc
    ext y
    simp only [RingHom.comp_apply]
    rw [← ComplexEmbedding.conjugate_coe_eq, e]
  have hpos : 0 < InfinitePlace.nrComplexPlaces K := by
    classical
    unfold InfinitePlace.nrComplexPlaces
    convert Fintype.card_pos_iff.2 (⟨⟨_, hcx⟩⟩ : Nonempty {w : InfinitePlace K // w.IsComplex})
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
  have huniq : ∀ w : InfinitePlace K, w = InfinitePlace.mk φK := fun w =>
    Fintype.card_le_one_iff.1 hcard.le w _
  have hp := InfinitePlace.prod_eq_abs_norm x
  have e : (∏ w : InfinitePlace K, w x ^ w.mult) = InfinitePlace.mk φK x ^ (InfinitePlace.mk φK).mult := by
    rw [Fintype.prod_eq_single (InfinitePlace.mk φK) fun w hw => absurd (huniq w) hw]
  rw [← hp, e, InfinitePlace.apply, InfinitePlace.mult_isComplex ⟨_, hcx⟩]

theorem nrm_pow_mul_norm_latDisc_eq {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair)
    (ha : IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa) (hb : IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb)
    (hcl : ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by

  have h1 : ClassGroup.mk K (𝔟 * 𝔞⁻¹) = 1 := by rw [map_mul, map_inv, ← hcl, mul_inv_cancel]
  obtain ⟨c, hcE⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hb' : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c * 𝔞 := by
    rw [← hcE, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply 𝔟.ne_zero
    rw [hb', FractionalIdeal.spanSingleton_zero, zero_mul]
  have hu : φK c ≠ 0 := (map_ne_zero φK).2 hc0

  have hlat : ∀ w, φK c * w ∈ Λb.lattice ↔ w ∈ Λa.lattice := by
    intro w
    have eb : φK c * w ∈ Λb.lattice ↔ φK c * w ∈ φK '' ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← hb]; rfl
    have ea : w ∈ Λa.lattice ↔ w ∈ φK '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← ha]; rfl
    rw [eb, ea]
    constructor
    · rintro ⟨y, hy, e⟩
      have hy' : y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) := hy
      rw [hb', FractionalIdeal.mem_singleton_mul] at hy'
      obtain ⟨y', hy', rfl⟩ := hy'
      refine ⟨y', hy', ?_⟩
      rw [map_mul] at e
      exact mul_left_cancel₀ hu e
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c * y, ?_, map_mul _ _ _⟩
      show c * y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
      rw [hb', FractionalIdeal.mem_singleton_mul]
      exact ⟨y, hy, rfl⟩
  have hD := latDisc_eq_of_mul Λa Λb (φK c) hu hlat

  have hN : nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = ‖φK c‖ ^ 2 * nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    unfold nrm
    rw [hb', map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, abs_norm_eq_norm_sq φK h2 hc c]
  rw [hN, hD, norm_mul, norm_pow]
  ring

end GlobalTheory.DiscClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorComplex
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem crossT_ι_eq_zero_of_vanish {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ)
    (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r)
    (hc : p < c) :
    (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  have ht : c + l = t := h
  by_cases hcl : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R (twX E V) a b).inv, comp_zero]
    refine free_ext _ _ fun U y => ?_
    have e1 := evT_crossT V ℓ μ hk α z a b r hr U y
    unfold evT at e1
    refine e1.trans ?_
    have h0 : ev α a _ rfl U (baseS V y) = 0 := by
      rw [ev_def, hα _ _ _ hc, comp_zero]
      exact map_zero (mapHom _ _ (freeGen R _ U (baseS V y)))
    rw [h0, map_zero, LinearMap.zero_apply, smul_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).symm
  · exact (biChains_isZero (R := R) (twX E V) c l (by omega)).eq_of_src _ _

end GlobalTheory.PBFc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorEmbedding
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc.AWCross

theorem idc_eq (M a : ℕ) (h : 0 + a ≤ M) : idc M a = SimplexCategory.subinterval 0 a h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (v : ℕ) = (v : ℕ) + 0
    have := v.2
    omega

theorem backc_eq (M a b : ℕ) (h : a + b ≤ M) : backc M a b = SimplexCategory.subinterval a b h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (a + (v : ℕ)) = (v : ℕ) + a
    have := v.2
    omega

variable {R : Type} [CommRing R]

theorem evT_of_eq {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (t s : ℤ)
    (ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -(b : ℤ)) = t)
    (h : t + n = s) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) t ht ≫
      γ.v t s h) (freeGen R _ U y) =
    evT γ a b s (by simp only [ComplexShape.π_def] at ht; push_cast; omega) U y := by
  obtain rfl : t = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at ht; push_cast; omega
  rfl

theorem map_comp_apply' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (y : Sec F U) :
    Sec.map (f ≫ g) y = Sec.map g (Sec.map f y) := rfl

theorem mapHom_apply' (F G : Shv R) {U : Scheme.{0}} (y : Sec F U) (φ : F ⟶ G) : mapHom F G y φ = Sec.map φ y := rfl

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem baseS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    baseS V ((awP (twX E V) M a (M - a)).app (op U) x) = (x.sub 0 a (by omega)).map (twPi E V) := by
  unfold awP
  rw [idc_eq M a (by omega)]
  rfl

theorem ell_nat (M p q : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk M)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk M) :
    ((twX E V).map θ.op).app (op (SimplexCategory.mk M)) ≫ ((twX E V).obj (op (SimplexCategory.mk p))).map β.op ≫
      (ℓ.app (op (SimplexCategory.mk p))).app (op (SimplexCategory.mk q)) =
    (ℓ.app (op (SimplexCategory.mk M))).app (op (SimplexCategory.mk M)) ≫ B.map β.op := by
  rw [(ℓ.app _).naturality, ← Category.assoc, ← NatTrans.comp_app, ℓ.naturality]
  simp

theorem vertS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    vertS V ℓ ((awP (twX E V) M a (M - a)).app (op U) x) =
      (x.sub a (M - a) (by omega)).map (bidiag.map ℓ ≫ (bidiagConst B).hom) := by
  unfold awP vertS
  rw [backc_eq M a (M - a) (by omega)]
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M a (M - a) (idc M a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M (M - a) (M - a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  exact h1.trans h2.symm
end Cross

theorem isAW_pull_crossT : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  intro R _ E N V B ℓ I J K μ n m k hk α z c hc M w h U x
  rw [ev_def, hc M w h]
  simp only [awZ, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp]
  change mapHom _ _ (freeGen R _ U x) (∑ a : Fin (M + 1), _) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mapHom_apply', map_comp_apply', freeGen_map, evT_of_eq, evT_crossT, ev_pull, ev_pull, baseS_aw V M (a : ℕ) (by omega), vertS_aw V ℓ M (a : ℕ) (by omega)]

end GlobalTheory.PBFc.AWCross

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherFormsOneCocycleCoboundaryOfRestrictStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), Function.Injective (CoefMap.restrict (FormExtJ.omjExt F j) G).pull1 → (∀ κ : W1 F j, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F j ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F j (G.map a) (θ' t)) → ∃ θ : W0 F j, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F j φ (θ T)) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary | exact GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary | (intros; apply GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero : ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q)), (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) - freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0 → (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.relation_kernel
  | exact GlobalTheory.EtC.KummerSplit.relation_kernel
  | (intros; apply GlobalTheory.EtC.KummerSplit.relation_kernel <;> assumption)
end

