module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsCxOfFactor
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosDExactGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFactorAssociatedJacobian
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscriminantEqJacobianCompleteIntersectionDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.DiscrJacGlobal
open EtBaseChange

theorem top_le_of_closedPoint {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) {U : X.Opens}
    (h : w (IsLocalRing.closedPoint T) ∈ U) : ⊤ ≤ w ⁻¹ᵁ U :=
  fun p _ => ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open U.isOpen h

theorem exists_unit_chart {R T : Type} [CommRing R] [CommRing T] (x : KeyIn R) (w : Sp T ⟶ x.P.A.left)
    (c c' : x.P.L.ι) (h : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c') :
    ∃ ω : Tˣ, ∀ (l : ℕ) (s : RR x l), valT w (x.P.L.U c) (s.f c) = (ω : T) ^ l * valT w (x.P.L.U c') (s.f c') := by
  have hp : ⊤ ≤ w ⁻¹ᵁ (x.P.L.U c ⊓ x.P.L.U c') := fun p hp => ⟨h hp, h' hp⟩
  refine ⟨Units.map (valH w _ hp).toMonoidHom (x.P.L.g c c'), fun l s => ?_⟩
  have hs : rs x.P.A.left (inf_le_left : x.P.L.U c ⊓ x.P.L.U c' ≤ x.P.L.U c) (s.f c) =
      ((x.P.L.g c c' ^ (l : ℤ) : Γ(x.P.A.left, x.P.L.U c ⊓ x.P.L.U c')ˣ) : Γ(x.P.A.left, x.P.L.U c ⊓ x.P.L.U c')) *
        rs x.P.A.left inf_le_right (s.f c') := s.compat c c'
  refine (valT_res w inf_le_left hp _).symm.trans ((congrArg (valT w _) hs).trans ?_)
  refine (valT_eq w _ hp _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
  · rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]; rfl
  · exact (valT_eq w _ hp _).symm.trans (valT_res w _ hp _)

theorem notMem_nonzeroLocus {R T : Type} [CommRing R] [CommRing T] [IsLocalRing T] (x : KeyIn R)
    (w : Sp T ⟶ x.P.A.left) (c : x.P.L.ι) (h : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c) {l : ℕ} (s : RR x l)
    (hs : valT w (x.P.L.U c) (s.f c) = 0) : w (IsLocalRing.closedPoint T) ∉ Out.nonzeroLocus s := by
  intro hy
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have h₁ := top_le_of_closedPoint w hk
  have hle := x.P.A.left.basicOpen_le (s.f k)
  obtain ⟨ω, hω⟩ := exists_unit_chart x w k c (fun p hp => hle (h₁ hp)) h
  have e := valT_res w hle h₁ (s.f k)
  rw [valT_eq w _ h₁] at e
  have hu : IsUnit (valT w (x.P.L.U k) (s.f k)) :=
    e ▸ (x.P.A.left.toRingedSpace.isUnit_res_basicOpen (s.f k)).map (valH w _ h₁)
  rw [hω, hs, mul_zero] at hu
  exact not_isUnit_zero hu

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (π : X ⟶ Sp R) (f : R →+* T)
    (w : Sp T ⟶ X) (hw : w ≫ π = spMap f) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (c : R) :
    valT w U (cst π U c) = f c := by
  have h0 : valT w U (cst π U c) =
      valT w U ((π.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE w π (U := ⊤) le_top h _).trans ?_)
  rw [hw, ← Category.comp_id (spMap f), valT_spMap f (𝟙 (Sp R)) (U := ⊤) le_top, valT_eq (𝟙 (Sp R)) ⊤ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  simp

theorem eval_det_pderiv_mul {O : Type} [CommRing O] {g : ℕ} (e : MvPowerSeries (Fin g) O →ₐ[O] O)
    (ω : MvPowerSeries (Fin g) O) (F : Fin g → MvPowerSeries (Fin g) O) (hF : ∀ i, e (F i) = 0) :
    e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (ω * F i)).det =
      e ω ^ g * e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (F i)).det := by
  rw [AlgHom.map_det, AlgHom.map_det]
  refine Eq.trans ?_ ((Matrix.det_smul _ (e ω)).trans (by rw [Fintype.card_fin]))
  congr 1
  ext i j
  simp [hF]

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, GlobalTheory.KeyKa.jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O) (Pm : Matrix (Fin d) (Fin d) O) (t₀ : O), (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) = Pm * ev₀ 0 ∧ IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) ∧ TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) t₀ ∧ Associated (Pm.det ^ 2) (∏ a, GlobalTheory.KeyKa.jac x s (z a) (ch a)) := by
  intro laws O _ _ _ _ x n l d s b m z ch hn hl hb hm hfin hz hs hj hinj hex
  classical
  let p₀ : Fin d → x.P.A.left := fun a => (z a).left (IsLocalRing.closedPoint O)
  let Y : Type := Set.range p₀
  let p : Fin d → Y := fun a => ⟨p₀ a, a, rfl⟩
  have hY : Finite Y := (Set.finite_range p₀).to_subtype
  choose r hr using fun y : Y => y.2
  choose θ hθ₀ hθ₁ hθ₂ hθ₃ using fun y : Y =>
    GlobalTheory.FormalChart.exists_formal_chart O x.P.A.left x.P.A.hom x.P.g (z (r y)).left x.P.smoothDim (Over.w (z (r y)))
  have hθ : ∀ y : Y, θ y (IsLocalRing.closedPoint _) = y.1 := fun y => (hθ₀ y).trans (hr y)
  choose e he₁ he₂ using fun a => hθ₃ (p a) O (z a).left
    ((Over.w (z a)).trans (Spec.map_id _).symm) (hθ (p a)).symm
  have hc : ∀ y, ⊤ ≤ θ y ⁻¹ᵁ x.P.L.U (ch (r y)) := fun y => top_le_of_closedPoint _ (by
    rw [hθ₀]; exact hz (r y) (x := IsLocalRing.closedPoint O) trivial)
  have hc' : ∀ a, ⊤ ≤ θ (p a) ⁻¹ᵁ x.P.L.U (ch a) := fun a => top_le_of_closedPoint _ (by
    rw [hθ]; exact hz a (x := IsLocalRing.closedPoint O) trivial)
  choose ω hω using fun a => exists_unit_chart x (θ (p a)) (ch a) (ch (r (p a))) (hc' a) (hc (p a))
  let F : Y → Fin x.P.g → MvPowerSeries (Fin x.P.g) O := fun y i =>
    valT (θ y) (x.P.L.U (ch (r y))) ((s i).f (ch (r y)))
  let ρ : ∀ j, Y → Fin ((l - j * n) ^ x.P.g) → MvPowerSeries (Fin x.P.g) O := fun j y k =>
    valT (θ y) (x.P.L.U (ch (r y))) ((b j k).f (ch (r y)))
  let u : Fin d → Oˣ := fun a => Units.map (e a).toMonoidHom (ω a)
  have hval : ∀ a (k : ℕ) (sg : RR x k), valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a)) =
      (u a : O) ^ k * e a (valT (θ (p a)) (x.P.L.U (ch (r (p a)))) (sg.f (ch (r (p a))))) := fun a k sg => by
    have h := valT_spMap (e a).toRingHom (θ (p a)) (hc' a) (sg.f (ch a))
    rw [he₂, hω, map_mul, map_pow] at h
    exact h
  have hF : ∀ a i, e a (F (p a) i) = 0 := fun a i =>
    ((u a).isUnit.pow n).mul_right_eq_zero.1 ((hval a n (s i)).symm.trans (hs a i))
  have hZ : FinZ x s := by
    have : Finite (Sp O) := by
      refine Set.finite_univ_iff.1 ((Set.toFinite {(⊥ : PrimeSpectrum O), IsLocalRing.closedPoint O}).subset
        fun q _ => ?_)
      by_cases hq : PrimeSpectrum.asIdeal q = ⊥
      · exact Or.inl (PrimeSpectrum.ext hq)
      · exact Or.inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime q).isMaximal hq)))
    refine (hfin.union (Set.finite_range fun q : Fin d × Sp O => (z q.1).left q.2)).subset fun y hy => ?_
    by_cases h : x.P.A.hom y = IsLocalRing.closedPoint O
    · exact Or.inl ⟨h, hy⟩
    · obtain ⟨a, q, hq⟩ := hex y h hy
      exact Or.inr ⟨(a, q), hq⟩
  have hcx := (KoszulCx.koszul_isCx O x n l d s b z ch hl hb).2 m hm hz hs
  have hcl := GlobalTheory.KosResidueExact.main laws O _ (IsLocalRing.residue O) x n l s b m hn hl hb hm hZ
  have hgen := GlobalTheory.KeyKa.KoszulGenExact.kosD_exact_generic laws O _ (algebraMap O (FractionRing O)) x n l s b m d z ch
    (IsFractionRing.injective O _) hn hl hb hm hz hs hj hinj (fun y ⟨q, hq⟩ => hex y fun h => by
      have h₁ := congrArg PrimeSpectrum.asIdeal (hq.trans h)
      have h₂ : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right q.isPrime.ne_top
      change Ideal.comap (algebraMap O (FractionRing O)) q.asIdeal = IsLocalRing.maximalIdeal O at h₁
      rw [h₂, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O _)] at h₁
      exact IsDiscreteValuationRing.not_a_field O h₁.symm)
  obtain ⟨hK₁, hK₂⟩ := GlobalTheory.KeyKa.KosKer.ker_and_image O x.P.g d _ m _ hcx hgen hcl
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let f : O →+* K := (algebraMap (IsLocalRing.ResidueField O) K).comp (IsLocalRing.residue O)
  have hf : RingHom.ker f = IsLocalRing.maximalIdeal O := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (IsLocalRing.ResidueField O) K).injective]
    exact IsLocalRing.ker_residue
  have hsurj := GlobalTheory.SeriesNakayama.span_mod_equations_lift O K f x.P.g _ Y F (ρ 0) hf (GlobalTheory.KeyKa.exists_sub_mem_of_dense K x.P.g _ Y _ _
    (GlobalTheory.KeyKa.exists_comb_sub_mem_sup_pow laws O K f x n l s b m Y θ (fun y => ch (r y)) hf hn hl hb hm hZ hθ₁ hθ₂ hc
      (fun y y' h => Subtype.ext ((hθ y).symm.trans (h.trans (hθ y'))))
      (fun y i => by
        rw [hθ₀]
        exact notMem_nonzeroLocus (T := O) x _ _ (hz (r y)) _ (hs (r y) i))))
  have hmul : ∀ y i k, F y i * ρ 1 y k = ∑ k', m i 0 1 k' k • ρ 0 y k' := fun y i k => by
    have h := congrArg (valH (θ y) _ (hc y)) (hm i 0 i.pos k (ch (r y)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum] at h
    refine (congrArg₂ (· * ·) (valT_eq _ _ (hc y) _) (valT_eq _ _ (hc y) _)).trans
      (h.trans (Finset.sum_congr rfl fun k' _ => (map_mul _ _ _).trans ?_))
    rw [Algebra.smul_def]
    exact congrArg₂ (· * ·) ((valT_eq _ _ (hc y) _).symm.trans (valT_cst x.P.A.hom _ (θ y) (hθ₁ y) _ (hc y) _))
      (valT_eq _ _ (hc y) _).symm
  obtain ⟨E, Pm, h₁, h₂, h₃, h₄⟩ := GlobalTheory.DiscrJacobianBlocks.exists_factor_associated_jacobian O x.P.g d _ Y p F (ρ 0) e (fun a => u a ^ (l - 0 * n))
    (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) hF he₁
    (fun a k => hval a _ (b 0 k)) hsurj (fun v hv y => by
      obtain ⟨w, rfl⟩ := hK₁ v hv
      have : ∑ k, (∑ i, (m i 0 1).mulVec (w i)) k • ρ 0 y k = ∑ i, ∑ k', w i k' • (F y i * ρ 1 y k') := by
        simp only [hmul, Finset.sum_apply, Finset.sum_smul, Finset.smul_sum, Matrix.mulVec, dotProduct, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp only [_root_.mul_comm]
      rw [this]
      exact Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun k' _ => Submodule.smul_of_tower_mem _ _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))) hK₂
  let ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O := fun j => Nat.casesOn j E fun _ => 0
  obtain ⟨h₅, t₀, h₆⟩ := GlobalTheory.KeyKa.KoszulTors.koszul_tors O x.P.g d _ m _ ev₀ Pm hcx h₁ h₂ h₃ hK₁ hcl
  refine ⟨ev₀, Pm, t₀, h₁, h₅, h₆, h₄.trans (Associated.prod _ _ _ fun a _ => ?_)⟩
  obtain ⟨v, hv⟩ := GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv O x (θ (p a)) (z a) (e a) (hθ₁ _) (hθ₂ _) (hθ₃ _) (he₁ a) (he₂ a)
  rw [hv n s (ch a) (hz a)]
  simp only [hω]
  rw [eval_det_pderiv_mul (e a) _ (F (p a)) (hF a), ← _root_.mul_assoc]
  exact (associated_unit_mul_right _ _ (v.isUnit.mul ((((ω a).isUnit.pow n).map (e a)).pow _)))

end GlobalTheory.DiscrJacGlobal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAlgClosedTransversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_enum_torsion (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (x : KeyIn K) (N : ℕ)
    (hN : (N : K) ≠ 0) : ∃ ξ : Fin (N ^ (2 * x.P.g)) → Pt x, (∀ a, ξ a ^ N = 1) ∧
      ∀ a a', a ≠ a' → ∀ p : Sp K, (ξ a).left p ≠ (ξ a').left p := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  have hc : Nat.card {y : Pt x // y ^ N = 1} = N ^ (2 * x.P.g) :=
    (hL.mulN _ x.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 K (𝟙 _) hN
  have : Finite {y : Pt x // y ^ N = 1} := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ hN0)
  let e := (Finite.equivFinOfCardEq hc).symm
  refine ⟨fun a => (e a).1, fun a => (e a).2, fun a a' h p hp => h (e.injective (Subtype.ext ?_))⟩
  have := x.P.isAb.proper
  obtain rfl : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq x.P.A.hom (Over.w _) (Over.w _) hp)

theorem exists_kaVal_of_isAlgClosed : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), admitted x.P.g n l l' al → ((degProd x.P.g n l l' : ℕ) : K) ≠ 0 → EtZ x s z ch → ∃ κ, KaVal x n l l' al s κ := by
  intro hL K _ _ x n l l' al d s z ch hA hN hZ
  obtain ⟨ξ, h₁, h₂⟩ := exists_enum_torsion hL x _ hN
  exact _root_.GlobalTheory.exists_kaVal_of_split hL K x n l l' al d s z ch ξ hA (Ne.isUnit hN) hZ h₁ h₂

end GlobalTheory.KeyKa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTwStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidTranslate_principalPolarisation_order_two : Out.Laws → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (t : 𝟙_ (Over (Sp R)) ⟶ P.A), t ^ 2 = 1 → ∃ (P' : Out.PolAV (Sp R)) (e : P'.A ≅ P.A), IsMonHom e.hom ∧ P'.g = P.g ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ LBIso P'.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left, (toUnit P'.A ≫ t).left] ![1, -1]) := by
  first | exact @GlobalTheory.RigidTranslate.exists_rigid_translate | exact GlobalTheory.RigidTranslate.exists_rigid_translate | (intros; apply GlobalTheory.RigidTranslate.exists_rigid_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyComplexPointEqOfSamePeriodMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegelPointUnique
open GlobalTheory.SiegelPullComp

def TriplePB {J : Type} {S S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lev' : J → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lev : J → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧ IsSquare φ φ₂ ∧ LBIso P' (P.pull φ₂) ∧
      ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left

variable {J : Type} {S S' S'' : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (A ⊗ A).left}
  {lev : J → (𝟙_ (Over S) ⟶ A)} {A' : Over S'} [GrpObj A'] {P' : LB (A' ⊗ A').left}
  {lev' : J → (𝟙_ (Over S') ⟶ A')} {A'' : Over S''} [GrpObj A''] {P'' : LB (A'' ⊗ A'').left}
  {lev'' : J → (𝟙_ (Over S'') ⟶ A'')} {f : S' ⟶ S} {f' : S'' ⟶ S'}

theorem TriplePB.comp (hP : P.IsLB) (hP' : P'.IsLB) (hP'' : P''.IsLB) (m : TriplePB A' P' lev' A P lev f)
    (m' : TriplePB A'' P'' lev'' A' P' lev' f') : TriplePB A'' P'' lev'' A P lev (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, ⟨?_, ?_⟩, ?_, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans hP'' (pull_isLB hP' _) (pull_isLB (pull_isLB hP _) _) (iso_pull ψ₂ hw)).trans
      hP'' (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (iso_pull_pull hP φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem TriplePB.cancel (hP : P.IsLB) (hP' : P'.IsLB) (hP'' : P''.IsLB) (m : TriplePB A' P' lev' A P lev f)
    (n : TriplePB A'' P'' lev'' A P lev (f' ≫ f)) : TriplePB A'' P'' lev'' A' P' lev' f' := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨χ, χ₂, hχ, hs', hw', hl'⟩ := n
  have hp := hφ.1
  let F : A''.left ⟶ A'.left := hp.lift χ (A''.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ A'.hom = A''.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((A'' ⊗ A'').hom ≫ f') ⟶ A' ⊗ A' :=
    lift (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A''))
  let F₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left := U.left
  have h₁ : F₂ ≫ (fst A' A').left = (fst A'' A'').left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A'')))
  have h₂ : F₂ ≫ (snd A' A').left = (snd A'' A'').left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst A'' A'')) (pushPt hFw (snd A'' A'')))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans hP'' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
      (iso_pull_pull hP φ₂ F₂).symm).trans hP'' (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (lev'' a).left ≫ A''.hom = 𝟙 S'' := Over.w (lev'' a)
      have a₂ : (lev' a).left ≫ A'.hom = 𝟙 S' := Over.w (lev' a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem eq_of_ptAt : Out.Laws → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ → p = q := by
  intro hL hU h k K _ ζ σ F _ _ _ _ τ p q hp hq ⟨P, lev, φ, hper, ⟨hφ, _, φ₂, hs, hw⟩, hl⟩
    ⟨P', lev', φ', hper', ⟨hφ', _, φ₂', hs', hw'⟩, hl'⟩
  obtain ⟨c, hc⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h k K K ζ ζ (RingHom.id K) _ _ F.s (p ≫ F.s) p rfl
    (by rw [show spMap (RingHom.id K) = 𝟙 (Sp K) from Spec.map_id _, Category.comp_id])).1 F.univ
  obtain ⟨e, he, ⟨e₂, hes, hew⟩, hel⟩ := _root_.GlobalTheory.KeyFam.exists_iso_of_perLev hL hU h k τ P' P lev' lev hper' hper
  have l : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have l' : (abelian₂ P'.A P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have m : TriplePB P.A (abelian₂ P.A P.L) lev F.univ.A F.univ.P F.univ.lev p := ⟨φ, φ₂, hφ, hs, hw, hl⟩
  have m' : TriplePB P'.A (abelian₂ P'.A P'.L) lev' F.univ.A F.univ.P F.univ.lev q := ⟨φ', φ₂', hφ', hs', hw', hl'⟩
  have n : TriplePB c.A c.P c.lev F.univ.A F.univ.P F.univ.lev (𝟙 _ ≫ p) := by
    rw [Category.id_comp]; exact hc
  have i : TriplePB P.A (abelian₂ P.A P.L) lev P'.A (abelian₂ P'.A P'.L) lev' (𝟙 _) :=
    ⟨e.hom.left, e₂, Geo.Tor.isGrpPullback_of_iso e, hes, hew, fun a =>
      (congrArg (fun t => t.left) (hel a)).trans (Category.id_comp _).symm⟩
  have r := m'.comp F.univ.isLB l' c.isLB (i.comp l' l c.isLB (m.cancel F.univ.isLB l c.isLB n))
  rw [Category.id_comp, Category.id_comp] at r
  exact F.inj ℂ p q _ c (hp.trans hq.symm) hc r

end GlobalTheory.SiegelPointUnique
end
end

