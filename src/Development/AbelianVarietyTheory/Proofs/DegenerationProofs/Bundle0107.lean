module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcAbelianLocusAndModuliOfTraitData
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory
namespace ArcLocus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem closedPoint_notMem (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (f : O' →+* R) (u : R)
    (χ : Sp R ⟶ Y.X) (h : Y.HasArcData a (IsLocalRing.maximalIdeal R) f u χ) :
    χ (IsLocalRing.closedPoint R) ∉ abLocus Y.t.G := by
  intro h₁
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ f u χ).1 h
  have h₂ := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 _).1 h₁
  have hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  obtain ⟨p, hp⟩ : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]
    exact le_refl (IsLocalRing.maximalIdeal R)
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick R (IsLocalRing.maximalIdeal R) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial a.D₀.X := a.nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (x : PrimeSpectrum R)
    (hx : x.asIdeal ≠ ⊥) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), CDvr W ∧ (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      (IsLocalRing.maximalIdeal W).comap φ = x.asIdeal := by
  obtain ⟨W, _, _, _, _, φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) x.asIdeal (bot_lt_iff_ne_bot.2 hx)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
  have hφ' : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  exact ⟨W, inferInstance, inferInstance, inferInstance, φ, IsFractionRing.lift hφ',
    ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩,
    fun r => IsFractionRing.lift_algebraMap hφ' r, h2⟩

theorem j_mem (Y : Model Xo c β) (p : Xo.XF c) : Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact hz

theorem mem_range_j (Y : Model Xo c β) (z : Y.X) (hz : z ∈ abLocus Y.t.G) (p : Xo.XF c)
    (hp : Y.s z = Y.s (Y.j p)) : z ∈ Set.range Y.j := by
  have h₁ : z ∈ Set.range (pullback.fst Y.s (spMap β)) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hp]
    have : Y.j p ∈ Set.range (pullback.fst Y.s (spMap β)) := ⟨Y.jQ p, rfl⟩
    rwa [Scheme.Pullback.range_fst] at this
  obtain ⟨w, rfl⟩ := h₁
  have h₂ : w ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hz
  obtain ⟨q, rfl⟩ := h₂
  exact ⟨q, rfl⟩

theorem exists_jK_eq_bot (R : Type) [CommRing R] [IsDomain R] :
    ∃ pt : Sp (FractionRing R), jK R pt = (⊥ : PrimeSpectrum R) := by
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

end ArcLocus


open ArcLocus in
theorem arc_abLocus_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb y χ hχ hT
  have hN : IsNoetherianRing O' := by
    rcases hb with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have hc : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨pt, hpt⟩ := exists_jK_eq_bot (PowerSeries O')
  have h0 : χ (⊥ : PrimeSpectrum (PowerSeries O')) = Y.j (y pt) := by
    rw [← hpt, ← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]
  have h1 : χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have hd : IsDominant (jK (PowerSeries O')) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap (PowerSeries O') (FractionRing (PowerSeries O')))).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (PowerSeries O') _)]; exact bot_le)
    refine ext_of_isDominant (jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, hT.1]
    have : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal := by
    intro x
    by_cases hx : x.asIdeal = ⊥
    · have e : x = (⊥ : PrimeSpectrum (PowerSeries O')) := PrimeSpectrum.ext hx
      refine iff_of_true ?_ ?_
      · rw [e, h0]; exact j_mem Y _
      · rw [hx]; exact PowerSeries.X_ne_zero
    obtain ⟨W, _, _, _, φ, gam, hW, hg, hφ⟩ := exists_trait (PowerSeries O') x hx
    have key : spMap gam ≫ jK (PowerSeries O') = jK W ≫ spMap φ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext hg
    have ht := hT.2 W hW φ gam hg (spMap φ ≫ χ) (by rw [← hχ, ← Category.assoc, key, Category.assoc])
    have hu : PowerSeries.X ∉ x.asIdeal ↔ IsUnit (φ PowerSeries.X) := by
      rw [← hφ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hcl : spMap φ (IsLocalRing.closedPoint W) = x := PrimeSpectrum.ext hφ
    rw [hu]
    refine ⟨fun hab => ?_, fun h => ht.1 h ⟨IsLocalRing.closedPoint W, (Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)⟩⟩
    by_contra h
    obtain ⟨W', _, _, _, io, -, -, hfin, hA⟩ := ht.2 h
    refine closedPoint_notMem Y a _ _ _ hA ?_
    have hcl' : spMap io (IsLocalRing.closedPoint W') = IsLocalRing.closedPoint W := by
      refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' io hfin.to_isIntegral (IsLocalRing.maximalIdeal W')
    have e : (spMap io ≫ spMap φ ≫ χ) (IsLocalRing.closedPoint W') = χ x :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (spMap φ ≫ χ) hcl').trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)))
    rw [e]
    exact hab
  refine ⟨h1, h2, fun x hx => mem_range_j Y _ ((h2 x).2 fun h => hx (Ideal.mul_mem_left _ _ h)) (y pt) ?_⟩
  have hC : ∀ z : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ z.asIdeal →
      spMap (PowerSeries.C (R := O')) z = (⊥ : PrimeSpectrum O') := by
    intro z hz
    refine PrimeSpectrum.ext ?_
    change z.asIdeal.comap (PowerSeries.C (R := O')) = ⊥
    have hzp := z.isPrime
    rcases hb with h | h
    · letI := h.1.toField
      exact Ideal.eq_bot_of_prime _
    · have := h.1
      by_contra hne
      have hm := IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
      have : ϖ ∈ z.asIdeal.comap (PowerSeries.C (R := O')) := by
        rw [hm]; exact h.2.1.not_isUnit
      exact hz (Ideal.mul_mem_right _ _ this)
  have hb0 : spMap (PowerSeries.C (R := O')) (⊥ : PrimeSpectrum (PowerSeries O')) = (⊥ : PrimeSpectrum O') :=
    PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (PowerSeries.C_injective (R := O')))
  have h3 : ∀ z : Sp (PowerSeries O'), Y.s (χ z) = spMap b (spMap (PowerSeries.C (R := O')) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
  rw [← h0, h3, hC x hx]
  exact ((h3 _).trans (congrArg (spMap b) hb0)).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem psi_value_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.X) (hW : Match a f u P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (z : Sp F) (y : a.D₀.X) (χ : P.X) (hχ : e y = χ) (j : P.P.L.ι)
    (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  subst hχ
  obtain ⟨-, -, -, -, -, hG⟩ := hW
  have hG' := (genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)
  obtain ⟨hp, hv⟩ := hG'
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c (e y)).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c (e y)) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c (e y))) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hz₁ : (Out.jFK (R := O') F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by
    rw [← hp PUnit.unit]; exact hz₀
  have ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing O'))) ⁻¹ᵁ
      (LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) :=
    (top_le_iff_mem _ _ (Out.jFK (R := O') F z)).2 (Set.mem_iInter.2 fun _ => hz₁)
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap (algebraMap (FractionRing O') F) (𝟙 _) _ ht₀
    ((a.D₀.psi y).s (fun _ => j₀)) z
  obtain ⟨r, s, hs, hr⟩ := IsFractionRing.div_surjective (A := O') u₀.val
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := fun h0 => u₀.ne_zero (by rw [← hr, h0, map_zero, zero_div])
  obtain ⟨r', hr'⟩ := hf r hr0
  obtain ⟨s', hs'⟩ := hf s hs0
  have hq : algebraMap (FractionRing O') F u₀.val = g (r' * s'⁻¹).val := by
    rw [← hr, map_div₀, hF, hF, ← hr', ← hs', Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]
    rfl
  rw [hq, Category.comp_id] at hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * (r' * s'⁻¹), H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem pow_eq_of_not_isUnit {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {u : R} (hu : ¬ IsUnit u)
    (v v' : Rˣ) (m n : ℕ) (h0 : u ^ m * v ≠ 0) (h : u ^ m * v = u ^ n * v') : m = n := by
  by_cases hz : u = 0
  · subst hz
    have h0' := h ▸ h0
    have hm : m = 0 := by
      by_contra hm; exact h0 (by rw [zero_pow hm, zero_mul])
    have hn : n = 0 := by
      by_contra hn; exact h0' (by rw [zero_pow hn, zero_mul])
    omega
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨k, t, ht⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    have hk : k ≠ 0 := by
      rintro rfl
      exact hu (by rw [ht, pow_zero, _root_.mul_one]; exact t.isUnit)
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (t ^ m * v) (t ^ n * v') (k * m) (k * n) (by
      rw [ht] at h
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_mul]
      linear_combination h)
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) this

theorem be_self_eq_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (hu : ¬ IsUnit u) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X)
    (h₁ : Match a f u P oP φ₁ he₁ w₁ e₁) (h₂ : Match a f u P oP φ₂ he₂ w₂ e₂) (y y' : a.D₀.X) (hy : e₁ y = e₂ y') :
    a.be y y = a.be y' y' := by
  let F := AlgebraicClosure (FractionRing R)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective _ _)
  have hfi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun x hx => by
    by_contra h0
    exact (hf x h0).ne_zero hx
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.P.isLB ((P.c (e₁ y)).left (cpt R))
  obtain ⟨v, hv⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₁ he₁ w₁ e₁ h₁
    F _ _ _ alg hF z y _ rfl j hj
  obtain ⟨v', hv'⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₂ he₂ w₂ e₂ h₂
    F _ _ _ alg hF z y' _ hy.symm j hj
  have e := (toStk z).injective (hv.symm.trans hv')
  have e0 := fun h => Units.ne_zero _ (hv.trans ((congrArg (toStk z) h).trans (map_zero _)))
  have nn : ∀ y, 0 ≤ a.be y y := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · exact (a.be_pos y hy).le
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y) (by norm_num : (0 : ℤ) ≤ 2))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y') (by norm_num : (0 : ℤ) ≤ 2))
  rw [hm, hn, zpow_natCast, zpow_natCast] at e
  rw [hm, zpow_natCast] at e0
  have e' : u ^ m * v = u ^ n * v' := by
    apply hg
    rw [map_mul, map_mul, map_pow, map_pow]
    exact e
  have e0' : u ^ m * v ≠ 0 := fun h => e0 (by
    have := congrArg g h
    rw [map_mul, map_pow, map_zero] at this
    exact this)
  have hmn : m = n := pow_eq_of_not_isUnit hu v v' m n e0' e'
  have d : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have d' : (2 : ℤ) ∣ a.be y' y' := (Dvd.intro _ rfl).trans (a.be_dvd y' y')
  omega

theorem be_symm_eq_of_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ f u hf hu P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ y =>
    be_self_eq_of_match a f u hf hu P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ _ _ (by simp)

end GlobalTheory.LN

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqZeroOfPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.LatChar

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem mem_span_iff {p : ℕ} [Fact p.Prime] {J A : Type} [Fintype J] [Nonempty J] (B : Matrix J J (PadicAlgCl p))
    (hB : B.det ≠ 0) (T : Set A) (v : A → J → PadicAlgCl p) (κ : ℝ) (hκ : 0 < κ)
    (hle : ∀ a ∈ T, ∀ i, ‖B.mulVec (v a) i‖ ≤ κ)
    (hdet : ∀ c : J → OO p, (∀ a ∈ T, ‖∑ i, (c i : PadicAlgCl p) * B.mulVec (v a) i‖ < κ) →
      ∀ i, ‖(c i : PadicAlgCl p)‖ < 1) (e : J → PadicAlgCl p) :
    e ∈ Submodule.span (OO p) (Set.range B) ↔ ∀ a ∈ T, ‖e ⬝ᵥ v a‖ ≤ κ := by
  have key : ∀ (c : J → PadicAlgCl p) (w : J → PadicAlgCl p),
      (B.vecMul c) ⬝ᵥ w = ∑ i, c i * B.mulVec w i := fun c w => (Matrix.dotProduct_mulVec c B w).symm
  have hvec : ∀ c : J → OO p, ∑ i, c i • B i = B.vecMul fun i => (c i : PadicAlgCl p) := fun c => by
    ext j
    rw [Finset.sum_apply]
    rfl
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => B i) _).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ a ha
    rw [hvec, key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hκ.le fun i _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 (c i).2)).trans (hle a ha i)
  · intro h
    obtain ⟨c, rfl⟩ : ∃ c, B.vecMul c = e := ⟨B⁻¹.vecMul e, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖c i‖
    by_cases h1 : ‖c i₀‖ ≤ 1
    · exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 ((hi₀ i).trans h1)⟩, hvec _⟩
    exfalso
    rw [not_le] at h1
    have h0 : 0 < ‖c i₀‖ := one_pos.trans h1
    have h0' : c i₀ ≠ 0 := norm_pos_iff.1 h0
    have := hdet (fun i => ⟨c i / c i₀, (mem_OO_iff _).2 (by
      rw [norm_div]; exact (div_le_one h0).2 (hi₀ i))⟩) (fun a ha => by
        have h2 := h a ha
        rw [key] at h2
        have e : ∑ i, c i / c i₀ * B.mulVec (v a) i = (∑ i, c i * B.mulVec (v a) i) / c i₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        show ‖∑ i, c i / c i₀ * B.mulVec (v a) i‖ < κ
        rw [e, norm_div, div_lt_iff₀ h0]
        exact h2.trans_lt (lt_mul_of_one_lt_right hκ h1)) i₀
    simp [div_self h0'] at this

theorem mem_lattice_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)) (κ : ℝ), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → u.Link σ b → b.det ≠ 0 → 0 < κ → (∀ a ∈ l.yy.ker, IsGreatest (Set.range fun i => ‖(b.map (algebraMap _ (PadicAlgCl p))).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖) κ) → ∀ e : S.J → PadicAlgCl p, e ∈ Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p)))) ↔ ∀ a ∈ l.yy.ker, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ κ := by
  intro L o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md b κ hBig hy hL hb hκ hmax e
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(_root_.GlobalTheory.ZH.utest_dim_and_split L o Ω S ρ p y₀ u).2.2.2.1, hBig.1, hBig.2.1⟩
  obtain ⟨hN, htor, -⟩ := _root_.GlobalTheory.ZH.special_torsion_eq_reduction L o Ω S ρ p y₀ u l σ cls md hy
  have pb : IsPullback md.r md.Φ.G.hom u.G.hom (rPt p ≫ spMap u.j) := md.cart.1
  have hs : Smooth u.G.hom := md.smooth.smooth
  have : Smooth md.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  refine mem_span_iff _ ?_ (l.yy.ker : Set S.Gam) (fun a i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) κ hκ
    (fun a ha i => (hmax a ha).2 ⟨i, rfl⟩) (fun c hc => ?_) e
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hb
  have hev : ∀ v : S.J → kb p, MvPolynomial.eval v (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) *
      MvPolynomial.X i) = ∑ i, IsLocalRing.residue (OO p) (c i) * v i := fun v => by simp
  have hz := _root_.GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion L.1 L.2.1 (kb p) md.Φ S.g S.N (S.r * S.N) _ S.J _ md.F md.pol hB md.good md.dim hN 1
    (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) * MvPolynomial.X i)
    (Nat.mul_pos (pow_pos (by have := hB.four; omega) _) (Nat.factorial_pos _))
    (MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X _ i).C_mul _) ?_
  · have h0 := lin_eq_zero md.Φ md.good (fun i => IsLocalRing.residue (OO p) (c i)) fun v hv =>
      (hev v).symm.trans (hz v hv)
    intro i
    exact (not_isUnit_OO_iff _).1 fun hu => (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu (congrFun h0 i)
  intro x hx
  obtain ⟨a, ha, z, a', hz, hg, hA, hr⟩ := htor x hx
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists md.isLB σ z
  obtain ⟨⟨i₀, -, hi₀⟩, x', hx', hc'⟩ := _root_.GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point L.1 L.2.1 p u.V u.j u.G S.g S.N (S.r * S.N) _ l.q _ S.J σ cls
    md hB z w hz hw
  have hxx : x'.left = x.left := pb.hom_ext (hx'.trans hr) ((Over.w x').trans (Over.w x).symm)
  refine ⟨_, hxx ▸ hc', ?_⟩
  have h1 := hL a' _ (hA ▸ (_root_.GlobalTheory.ZH.EvCrd.ev_crd_act L o Ω S ρ).1 _ y₀ a)
  have h2 := CrdCalc.crd_map (OO p).subtype hw
  rw [show spMap (OO p).subtype ≫ z = u.toG a' from hg] at h2
  obtain ⟨t, ht⟩ := CrdCalc.crd_unique h2 h1
  have hn : κ ≤ ‖(t : PadicAlgCl p)‖ := by
    obtain ⟨i, hi⟩ := (hmax a ha).1
    rw [← hi]
    beta_reduce
    rw [ht i, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 (w i).2)
  have h3 := hc a ha
  have e3 : ∑ i, (c i : PadicAlgCl p) * (b.map (algebraMap _ (PadicAlgCl p))).mulVec
      (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i = t * ((∑ i, c i * w i : OO p) : PadicAlgCl p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, c i * w i : OO p) : PadicAlgCl p) = (OO p).subtype (∑ i, c i * w i) from rfl, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, map_mul, mul_left_comm]
    rfl
  rw [e3, norm_mul] at h3
  have h4 : ‖((∑ i, c i * w i : OO p) : PadicAlgCl p)‖ < 1 := by
    by_contra h5
    exact absurd h3 (not_lt.2 (hn.trans (le_mul_of_one_le_right (norm_nonneg _) (not_lt.1 h5))))
  rw [hev]
  have h5 : IsLocalRing.residue (OO p) (∑ i, c i * w i) = 0 := by
    by_contra h6
    exact (not_isUnit_OO_iff _).2 h4 ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h6)
  simpa using h5

end GlobalTheory.ZH.LatChar
end

