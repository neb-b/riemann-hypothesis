module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

section Alg
variable {K : Type} [Field K]

theorem dualMap_fst {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).fst = f z.fst := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).fst = _
  simp

theorem dualMap_snd {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).snd = f z.snd := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).snd = _
  simp

theorem dn_snd_mul (u x : DualNumber K) : (u * x).snd = u.fst * x.snd + u.snd * x.fst := by
  rw [TrivSqZeroExt.snd_mul]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

theorem unit_fst_ne (u : (DualNumber K)ˣ) : (u : DualNumber K).fst ≠ 0 := by
  intro h
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at h1
  exact zero_ne_one h1

theorem unit_inv_fst (u : (DualNumber K)ˣ) : ((u⁻¹ : (DualNumber K)ˣ) : DualNumber K).fst = ((u : DualNumber K).fst)⁻¹ := by
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dualNumber_unit_mul_decomposition (U₁ : (DualNumber K)ˣ) (r : K) (hr : r ≠ 0) (P : DualNumber K) :
    (U₁ : DualNumber K) * P = TrivSqZeroExt.inl (((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst) *
      (TrivSqZeroExt.inl (P.fst / r) + TrivSqZeroExt.inr (P.snd / r +
        ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).snd / ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst * (P.fst / r))) := by
  have hu := unit_fst_ne U₁
  have e1 := dn_snd_mul (U₁ : DualNumber K) P
  have e2 := dn_snd_mul (U₁ : DualNumber K) (TrivSqZeroExt.inl r)
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    field_simp
  · rw [e1, dn_snd_mul]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, e2, add_zero, zero_add, mul_zero]
    field_simp
    ring

theorem fst_U (Θ T ω : (DualNumber K)ˣ) (k : ℕ) (r : K) :
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber K)ˣ) : DualNumber K) * TrivSqZeroExt.inl r).fst =
      (Θ : DualNumber K).fst * ((T : DualNumber K).fst)⁻¹ * (((ω : DualNumber K).fst)⁻¹) ^ k * r := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    TrivSqZeroExt.fst_inl, unit_inv_fst]

theorem fst_eq_of (θ τ ω g m r p : K) (k : ℕ) (hτ : τ ≠ 0) (hω : ω ≠ 0) (h1 : θ * g ^ k = p) (h2 : τ * m ^ k = r)
    (h3 : ω * g = m) : θ * τ⁻¹ * ω⁻¹ ^ k * r = p := by
  subst h1 h2 h3
  rw [mul_pow, inv_pow]
  field_simp

variable {Ix : Type}

theorem ds_mul_left {f : Ix → DualNumber K} {s : DualNumber K} [TopologicalSpace K] [IsTopologicalRing K] (u : DualNumber K)
    (h : HasSum (fun a => (f a).fst) s.fst ∧ HasSum (fun a => (f a).snd) s.snd) :
    HasSum (fun a => (u * f a).fst) (u * s).fst ∧ HasSum (fun a => (u * f a).snd) (u * s).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_mul]
    exact h.1.mul_left _
  · simp only [dn_snd_mul]
    exact (h.2.mul_left _).add (h.1.mul_left _)

theorem ds_sum {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] (f : Fin n → Ix → DualNumber K) (s : Fin n → DualNumber K)
    (h : ∀ i, HasSum (fun a => (f i a).fst) (s i).fst ∧ HasSum (fun a => (f i a).snd) (s i).snd) :
    HasSum (fun a => (∑ i, f i a).fst) (∑ i, s i).fst ∧ HasSum (fun a => (∑ i, f i a).snd) (∑ i, s i).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_sum]
    exact hasSum_sum fun i _ => (h i).1
  · simp only [TrivSqZeroExt.snd_sum]
    exact hasSum_sum fun i _ => (h i).2

private theorem isChart_choose_and_symm_apply {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}} (x : Sp B ⟶ X) (W : X.Opens)
    (h : x (IsLocalRing.closedPoint B) ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro p _
  have hle : (p : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  first
  | exact (hle.map x.continuous).mem_open W.isOpen h
  | exact (hle.map x.base.hom.continuous).mem_open W.isOpen h

end Alg

theorem value_at_tangent : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hν w₀ ρ hρ y gm₀ gm yA hy hrel hpull hvec k i₀ hi₀
  haveI : IsLocalRing (DualNumber V) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  obtain ⟨J0, hJ0⟩ := GlobalTheory.UU.exists_good_pt U.LG.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  obtain ⟨J1, hJ1⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  have hjG : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U (J0 y.left) := isChart_choose_and_symm_apply _ _ (hJ0 y.left)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J1 ψ) := fun ψ => isChart_choose_and_symm_apply _ _ (hJ1 ψ)
  have hgt : GtTan gm₀ := _root_.GlobalTheory.MBLow.TanRed.main V hV D A G hG U y gm₀ hy hrel
  obtain ⟨W, hW1, hW2⟩ := _root_.GlobalTheory.MBLow.TanExp.value_mul_sumI V hV D A G hG U y gm₀ hy hrel k (J0 y.left) J1 hjG hJ
  obtain ⟨T, hD, hT1, hT2⟩ := GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange V D.toPre C N ν gm₀ gm hgt hpull k J1 hJ
  obtain ⟨Θ, hΘ1, hΘ2⟩ := GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination V (IsLocalRing.maximalIdeal V) D A G U.toUnifPre C w₀ ρ hρ y yA hy hvec k i₀
    (J0 y.left) hi₀ hjG
  obtain ⟨ω, hω⟩ : ∃ ω : (DualNumber C)ˣ, (ω : DualNumber C) = dualMap (toF V C) (W : DualNumber V) :=
    ⟨Units.map (dualMap (toF V C)).toMonoidHom W, rfl⟩
  have hωfst : (ω : DualNumber C).fst = toF V C (W : DualNumber V).fst := by rw [hω, dualMap_fst]
  have h3 : (ω : DualNumber C).fst * toF V C (rigVal U.LG (J0 y.left)) =
      toF V C (rigValD D.toPre (J1 gm₀.b.left)) := by
    rw [hωfst, ← map_mul, hW1]
  have hinj : Function.Injective (toF V C) := by
    show Function.Injective ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    rw [RingHom.coe_comp]
    exact (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hm : toF V C (rigValD D.toPre (J1 gm₀.b.left)) ≠ 0 := by
    intro h0
    apply hD
    apply hinj
    rw [h0, map_zero]
  have hτ := unit_fst_ne T
  have hωne := unit_fst_ne ω
  have hr : ν.rg ^ k ≠ 0 := by
    rw [← hT1]
    exact mul_ne_zero hτ (pow_ne_zero _ hm)
  have hfst := (fst_U Θ T ω k (ν.rg ^ k)).trans (fst_eq_of _ _ _ _ _ _ _ k hτ hωne hΘ1 hT1 h3)
  refine ⟨(((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).snd /
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).fst, ?_⟩
  intro t s hts
  obtain ⟨σ', hcar, n, cc, σ, fa, hexp, hlin, hslin⟩ := hts
  have hA : ∀ i, HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).fst)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).fst ∧
      HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).snd)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).snd := by
    intro i
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.AdicDual.hasSum_fst_snd V (IsLocalRing.maximalIdeal V) C hC _ _ (hW2 (σ i) (fa i) (hexp i))
    simp only [dualMap_fst, dualMap_snd]
    exact ⟨(Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).fst) ν.eX.toEquiv).2 h1,
      (Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).snd) ν.eX.toEquiv).2 h2⟩
  have hB := ds_mul_left (T : DualNumber C)
    (ds_sum (fun i α => TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α))))
      _ (fun i => ds_mul_left (TrivSqZeroExt.inl (cc i)) (hA i)))
  have hjc := hT2 s n cc fa hslin
  simp only [← hjc] at hB
  obtain ⟨hf, hs⟩ := hB
  have hS : ((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * ((T : DualNumber C) *
      ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
      (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left)) := by
    simp only [map_mul, map_pow, ← hω]
    have e1 : ∀ i, TrivSqZeroExt.inl (cc i) * ((ω : DualNumber C) ^ k * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
        (ω : DualNumber C) ^ k * (TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) :=
      fun i => by ring
    simp only [e1, ← Finset.mul_sum]
    have hb : ((T⁻¹ : (DualNumber C)ˣ) : DualNumber C) * (T : DualNumber C) = 1 := Units.inv_mul T
    have hw : ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination ((Θ : DualNumber C) * (∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) *
        ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k) * hb +
      ((Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) * hw
  refine ⟨(hf.div_const _).summable, (hs.div_const _).summable, ?_⟩
  rw [(hf.div_const _).tsum_eq, (hs.div_const _).tsum_eq, hΘ2 t σ' hcar n cc σ hlin, ← hS, dualNumber_unit_mul_decomposition _ _ hr, hfst]

end GlobalTheory.MBLow.TanExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedData
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem exists_fracSpec {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem tauBimult_of_half : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R)
    (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) →
    D.TauBimult := by
  intro R _ _ R' _ _ Q ρ D e hρ h
  obtain ⟨κ, hκ⟩ := exists_fracSpec ρ hρ
  obtain ⟨β, β₂, w, hpb, hsq, hgen, hnorm, hc, hper⟩ := h
  have per : ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J := by
    intro a b z J J' hJ hJ'
    have := hper κ hκ a b z J J' hJ hJ'
    rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this
  let k : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  have hQ : ∀ a a' b : Q.X, ∀ z J, Good Q.M.L z J →
      val (Q.tau (a + a') b) κ z J * @id ((TK R').left.presheaf.stalk z)ˣ
        (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub z J
        (k ≫ toUnit (TK R) ≫ Q.c a) (k ≫ toUnit (TK R) ≫ Q.c a') (k ≫ toUnit (TK R) ≫ Q.c b)) =
      val (Q.tau a b) κ z J * val (Q.tau a' b) κ z J := by
    intro a a' b z J hJ
    have hcorr : LB.Gen.Corr Q.M.L _ _ _ _ (LB.mulGen Q.M.L _ _ _ _ (Q.tau (a + a') b)
        (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
          (lift (toUnit (TK R) ≫ Q.c a) (lift (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau a b) (Q.tau a' b)) := by
      refine corr_of_val Q.M.isLB fun y J hJ => ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)).trans ?_
      rw [Category.id_comp]
      exact Q.tau_add a a' b y J hJ
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ hcorr κ).trans (val_mul hJ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_cub Q.cub k hJ _ _ _).symm
  intro a a' b
  refine corr_of_val D.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB y (K := PEmpty) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim)
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _)).trans ?_
  rw [Category.id_comp]
  have hx : toUnit (TK R') ≫ D.c (a + a') = (toUnit (TK R') ≫ D.c a) * (toUnit (TK R') ≫ D.c a') := by
    rw [D.c_add, padd, comp_lift_assoc, Hom.mul_def]
  have hu : ∀ χ : D.X, (k ≫ toUnit (TK R) ≫ Q.c (e χ)).left = (toUnit (TK R') ≫ D.c χ).left ≫ β := by
    intro χ
    simp only [Over.comp_left, Over.homMk_left, toUnit_left, Category.assoc, hc, k]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Over.Hom.left (Q.c (e χ))) hκ
  obtain ⟨-, hw⟩ := GlobalTheory.T.mumfordBundleIso_normalised_respects_laws _ _ Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub (spMap ρ) β β₂ w
    hpb D.P.isAb hsq hgen hnorm (TK R') (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)
    y J J' hJ hJ'
  have hw' := hw _ _ _ (hu a) (hu a') (hu b)
  rw [← hx] at hw'
  have hq := hQ (e a) (e a') (e b) y J hJ
  rw [← map_add (f := _)] at hq
  change val (D.tau (a + a') b) (𝟙 _) y J' * cubV D.cub y J' _ _ _ = _
  rw [per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ']
  calc _ = (lamVal w (lift (toUnit (TK R') ≫ D.c (a + a')) (toUnit (TK R') ≫ D.c b)).left y J J' *
        cubV D.cub y J' (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)) *
        val (Q.tau (e (a + a')) (e b)) κ y J := by ac_rfl
    _ = _ := by
      rw [hw']
      calc _ = lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left y J J' *
            lamVal w (lift (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)).left y J J' *
            (val (Q.tau (e (a + a')) (e b)) κ y J * @id ((TK R').left.presheaf.stalk y)ˣ
              (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub y J
              (k ≫ toUnit (TK R) ≫ Q.c (e a)) (k ≫ toUnit (TK R) ≫ Q.c (e a')) (k ≫ toUnit (TK R) ≫ Q.c (e b)))) := by
            ac_rfl
        _ = _ := by rw [hq]; ac_rfl

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGenerator
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautTau

section Core

variable {X X' P P' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_across (hL : L.IsLB) (hL' : L'.IsLB) (ψ : K → (P ⟶ X)) (ψ' : K → (P' ⟶ X')) (ε : K → ℤ)
    (β₂ : P' ⟶ P) (w : LB.Iso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull β₂)) (hw : w.IsGen) (p : Y ⟶ P')
    (b : LB.Gen (LB.LinComb L (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k))) (hb : b.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L' (fun k => p ≫ ψ' k) (fun k => -ε k)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val u r z J' = gm (r ≫ p) z _ (w.s (fun _ k => J ((r ≫ p) ≫ β₂ ≫ ψ k), fun k => J' ((r ≫ p) ≫ ψ' k))) *
          val b r z J := by
  have hC : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _
  have hC' : (LB.LinComb L' ψ' ε).IsLB := DVR.linComb_isLB _ hL' _ _
  have pw := (isGen_iff w).1 hw

  have wchg : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j j₂ : K → L.ι) (q q₂ : K → L'.ι),
      (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j k)) → (∀ k, (f ≫ p ≫ β₂ ≫ ψ k) z ∈ L.U (j₂ k)) →
      (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q k)) → (∀ k, (f ≫ p ≫ ψ' k) z ∈ L'.U (q₂ k)) →
      gw w (f ≫ p) z j q = (∏ k, gm (f ≫ p ≫ β₂ ≫ ψ k) z _ (L.g (j k) (j₂ k)) ^ ε k) *
        (∏ k, gm (f ≫ p ≫ ψ' k) z _ (L'.g (q k) (q₂ k)) ^ ε k)⁻¹ * gw w (f ≫ p) z j₂ q₂ := by
    intro Z f z j j₂ q q₂ hj hj₂ hq hq₂
    have m₁ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j := Set.mem_iInter.2 fun k => hj k
    have m₂ : β₂ ((f ≫ p) z) ∈ (LB.LinComb L ψ ε).U j₂ := Set.mem_iInter.2 fun k => hj₂ k
    have m₃ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q := Set.mem_iInter.2 fun k => hq k
    have m₄ : (f ≫ p) z ∈ (LB.LinComb L' ψ' ε).U q₂ := Set.mem_iInter.2 fun k => hq₂ k
    rw [pw Z (f ≫ p) z j j₂ q q₂ m₁ m₂ m₃ m₄]
    erw [gm_linComb L ψ ε ((f ≫ p) ≫ β₂) z j j₂ m₁ m₂, gm_linComb L' ψ' ε (f ≫ p) z q q₂ m₃ m₄]
    simp only [Category.assoc]
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' (fun k => p ≫ ψ' k) q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι),
        f z ∈ LB.wchart L' (fun k => p ≫ ψ' k) q → f z ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j →
        gm f z _ s = gw w (f ≫ p) z j q * gm f z _ (b.s j) := by
    intro q
    let W : (K → L.ι) → Y.Opens := fun j =>
      LB.wchart L' (fun k => p ≫ ψ' k) q ⊓ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j
    have l₀ : ∀ j, W j ≤ LB.wchart L' (fun k => p ≫ ψ' k) q := fun j => inf_le_left
    have l₁ : ∀ j, W j ≤ p ⁻¹ᵁ (((LB.LinComb L ψ ε).pull β₂).U (fun _ => j) ⊓ (LB.LinComb L' ψ' ε).U q) :=
      fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 k),
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 k⟩
    have l₂ : ∀ j, W j ≤ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := fun j => inf_le_right
    obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Y, W j)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : K → L.ι), f z ∈ W j →
        gm f z (W j) (u j) = gw w (f ≫ p) z j q * gm f z _ (b.s j) :=
      ⟨fun j => res (l₁ j) (pullU p _ (w.s (fun _ => j, q))) * res (l₂ j) (b.s j), fun Z f z j hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f z (l₁ j) hz _).trans (gm_pull f p z _ (l₁ j hz) _)) (gm_res f z (l₂ j) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hx, Set.mem_iInter.2 hj⟩) u (fun j j₂ x hx => by
        rw [hu _ (𝟙 Y) x j hx.1, hu _ (𝟙 Y) x j₂ hx.2]
        have a := wchg Y (𝟙 Y) x j j₂ q q (fun k => Set.mem_iInter.1 hx.1.2 k) (fun k => Set.mem_iInter.1 hx.2.2 k)
          (fun k => Set.mem_iInter.1 hx.1.1 k) (fun k => Set.mem_iInter.1 hx.1.1 k)
        have c := gen_trans hb (𝟙 Y) x hx.1.2 hx.2.2
        have one : (∏ k, gm (𝟙 Y ≫ p ≫ ψ' k) x _ (L'.g (q k) (q k)) ^ ε k) = 1 :=
          Finset.prod_eq_one fun k _ => by
            rw [gm_self hL' (𝟙 Y ≫ p ≫ ψ' k) x (show (𝟙 Y ≫ p ≫ ψ' k) x ∈ L'.U (q k) from Set.mem_iInter.1 hx.1.1 k),
              one_zpow]
        have hA : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j₂ k)) ^ ε k) *
            trF (L := L) (fun k => p ≫ β₂ ≫ ψ k) (fun k => -ε k) (𝟙 Y) x j j₂ = 1 := by
          rw [trF, ← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, _root_.mul_inv_cancel]
        rw [a, one, inv_one, _root_.mul_one]
        erw [c]
        rw [_root_.mul_mul_mul_comm, hA, _root_.one_mul]
        rfl)
    exact ⟨s, fun Z f z j hq hj => (gm_res f z (l₀ j) ⟨hq, hj⟩ s).symm.trans
      ((congrArg (gm f z (W j)) (hs j)).trans (hu Z f z j ⟨hq, hj⟩))⟩
  choose s hs using glue
  refine ⟨⟨s⟩, fun q q₂ => unit_ext fun x hx => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  swap
  · refine (hs (fun k => J' (r ≫ p ≫ ψ' k)) Z r z (fun k => J (r ≫ p ≫ β₂ ≫ ψ k)) (hJ'.mem (fun k => p ≫ ψ' k) r)
      (hJ.mem (fun k => p ≫ β₂ ≫ ψ k) r)).trans ?_
    congr 1
  choose j hj using fun k => exists_chart hL ((p ≫ β₂ ≫ ψ k) x)
  have mj : (𝟙 Y) x ∈ LB.wchart L (fun k => p ≫ β₂ ≫ ψ k) j := Set.mem_iInter.2 hj
  have e₁ := hs q Y (𝟙 Y) x j hx.1 mj
  have e₂ := hs q₂ Y (𝟙 Y) x j hx.2 mj
  have c := wchg Y (𝟙 Y) x j j q q₂ hj hj (fun k => Set.mem_iInter.1 hx.1 k) (fun k => Set.mem_iInter.1 hx.2 k)
  have one : (∏ k, gm (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x _ (L.g (j k) (j k)) ^ ε k) = 1 :=
    Finset.prod_eq_one fun k _ => by
      rw [gm_self hL (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x (show (𝟙 Y ≫ p ≫ β₂ ≫ ψ k) x ∈ L.U (j k) from hj k), one_zpow]
  rw [one, _root_.one_mul] at c
  have g := gm_linComb L' (fun k => p ≫ ψ' k) (fun k => -ε k) (𝟙 Y) x q q₂ hx.1 hx.2
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx]
  erw [g, e₁, e₂, c]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rw [_root_.mul_assoc]

end Core

section Main

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]

theorem toUnit_left' {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem ag_four {G : Type} [CommGroup G] (a b c d : G) :
    a⁻¹ * b * c * d⁻¹ = (a * b⁻¹ * c⁻¹ * d)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tauCoord_of_dataFrom (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ))
    (hD : DataFrom T iw s ε n Q e) (a b : Q.X) :
    ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      Q.TauCoord a b k := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  obtain ⟨k, hk, hval⟩ := hτ a b
  refine ⟨k, hk, ?_⟩
  let h : (𝟙_ (Over (Sp V))).left ⟶ (𝟙_ (Over (Sp W))).left := spMap iw
  let p : (𝟙_ (Over (Sp V))).left ⟶ (G2 Q.B).left := (lift (Q.c a) (Q.c b)).left
  have c0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have t0 : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))
  have hF1 : p ≫ β₂ = (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left := by
    apply pullback.hom_ext
    · show _ ≫ (fst T.B T.B).left = _ ≫ (fst T.B T.B).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd T.B T.B).left = _ ≫ (snd T.B T.B).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      rfl
  have px : (pushPt hpb.1.w (Q.c a)).left = h ≫ (T.c₀ ((n : ℤ) • e a)).left := hc a
  have py : (pushPt hpb.1.w (Q.c b)).left = h ≫ (T.c₀ ((n : ℤ) • e b)).left := hc b
  have pxy : (pushPt hpb.1.w (Q.c a) * pushPt hpb.1.w (Q.c b)).left =
      h ≫ (T.c₀ ((n : ℤ) • e a) * T.c₀ ((n : ℤ) • e b)).left := by
    have m := congrArg (fun q => q.left) (map_mul (pushHom hpb (𝟙_ (Over (Sp V)))) (Q.c a) (Q.c b))
    refine m.symm.trans ?_
    show (Q.c a * Q.c b).left ≫ β = _
    rw [← Q.c_add, hc, ← T.c₀_add, ← smul_add, ← map_add (f := _)]
  have p1 : (1 : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap iw) ⟶ T.B).left = h ≫ (1 : 𝟙_ (Over (Sp W)) ⟶ T.B).left := by
    have m := congrArg (fun q => q.left) (map_one (pushHom hpb (𝟙_ (Over (Sp V)))))
    refine m.symm.trans ?_
    show (1 : 𝟙_ (Over (Sp V)) ⟶ Q.B).left ≫ β = _
    have := hc 0
    rw [c0, map_zero, smul_zero, t0] at this
    exact this
  have hFT : FormEq (fun k => h ≫ lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) k) negε
      (fun I => p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I) := by
    intro U _ H
    have r₁ : ∀ I, p ≫ β₂ ≫ GlobalTheory.PrimCocycle.lamφ T.B I =
        (lift (pushPt hpb.1.w (Q.c a)) (pushPt hpb.1.w (Q.c b))).left ≫ GlobalTheory.PrimCocycle.lamφ T.B I := fun I => by
      rw [← Category.assoc, hF1]
    simp only [r₁, zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, pxy, px, py, p1, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact ag_four _ _ _ _
  have hFQ : FormEq (fun I => p ≫ GlobalTheory.PrimCocycle.lamφ Q.B I) (fun I => -GlobalTheory.PrimCocycle.lamε I)
      (lamPts (Q.c a) (Q.c b)) negε := by
    intro U _ H
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [GlobalTheory.PrimCocycle.prod_lam, Fin.prod_univ_four]
    simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    exact (ag_four _ _ _ _).symm
  obtain ⟨b₁, hb₁, hv₁⟩ := exists_gen T.M.isLB hFT
    (LB.pullGen T.M.L (lamPts (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))) negε (T.τ₀ _ _) h)
    (DVR.pullGen_isGen _ _ _ _ (T.τ₀_gen _ _) h)
  obtain ⟨u₁, hu₁, hvu⟩ := exists_gen_across T.M.isLB Q.M.isLB (GlobalTheory.PrimCocycle.lamφ T.B)
    (GlobalTheory.PrimCocycle.lamφ Q.B) GlobalTheory.PrimCocycle.lamε β₂ w hw p b₁ hb₁
  obtain ⟨u, hu, hvq⟩ := exists_gen Q.M.isLB hFQ u₁ hu₁
  refine ⟨u, hu, fun z J' hJ' => ?_⟩
  choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
  have hJg : Good T.M.L z J := hJ
  rw [hval z J J' hJg hJ']
  congr 1
  rw [hvq _ _ z J' hJ', hvu _ _ z J J' hJg hJ', hv₁ _ _ z J hJg, val_pull hJg]
  have hr : (toUnit (TK V)).left ≫ p = (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left := by
    rw [← Over.comp_left, comp_lift]
  have hh : (toUnit (TK V)).left ≫ h = (TK V).hom ≫ spMap iw := by
    rw [toUnit_left']
  rw [hh, ← hr]
  rfl

end Main

end GlobalTheory.TautTau
end
end

