module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCombSubMemSupPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.ClosedApprox
open EtBaseChange

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (p : X ⟶ Sp R) (w : Sp T ⟶ X) (F : R →+* T)
    (hw : w ≫ p = spMap F) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (c : R) : valT w U (AbLaw.cst p U c) = F c := by
  have h0 : valT w U (AbLaw.cst p U c) =
      valT w U ((p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE w p (U := ⊤) le_top h _).trans ?_)
  rw [hw, ← Category.comp_id (spMap F)]
  refine (valT_spMap F (𝟙 (Sp R)) le_top _).trans (congrArg F ((valT_eq _ _ le_top _).trans ?_))
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  exact congrArg (fun q => q.hom c) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id

theorem top_le_of_closedPoint {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) {U : X.Opens}
    (h : w (IsLocalRing.closedPoint T) ∈ U) : ⊤ ≤ w ⁻¹ᵁ U := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open U.isOpen h

theorem exists_stalk_hom {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) (z : X)
    (hz : w (IsLocalRing.closedPoint T) = z) : ∃ ψ : X.presheaf.stalk z →+* T, ∀ (U : X.Opens), z ∈ U →
      ∀ a : Γ(X, U), valT w U a = ψ (gs (𝟙 X) z U a) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : X.presheaf.stalk z ⟶ .of T, Spec.map φ ≫ X.fromSpecStalk z = w := by
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w⟩
  refine ⟨φ.hom, fun U hU a => ?_⟩
  rw [← hφ, JacGen.valT_specMap_fromSpecStalk hU, gs_eq (𝟙 X) z U hU]
  rfl

theorem exists_mem_sub_mem_pow {σ K : Type} [Finite σ] [CommRing K] (S : Subring (MvPowerSeries σ K))
    (hC : ∀ a, algebraMap K _ a ∈ S) (hX : ∀ i, MvPowerSeries.X i ∈ S) (r : ℕ) (G : MvPowerSeries σ K) :
    ∃ p ∈ S, G - p ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) ^ r := by
  have key : ∀ q : MvPolynomial σ K, (q : MvPowerSeries σ K) ∈ S := fun q => by
    induction q using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.coe_C]; exact hC a
    | add p q hp hq => simpa using S.add_mem hp hq
    | mul_X p i hp => simpa using S.mul_mem hp (hX i)
  refine ⟨_, key (MvPowerSeries.truncTotal r G), ?_⟩
  rw [← germIdeal_eq_span, mem_germIdeal_pow_iff]
  intro d hd
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hd, sub_self]

theorem mem_nonzeroLocus_of_via {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} {l : ℕ} {s' : RR x' l} {s : RR x l}
    (hs : SecVia x' x φ w s' s) (y : x'.P.A.left) (hy : y ∈ Out.nonzeroLocus s') : φ y ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨k, hk⟩ := exists_chart x.P.isLB (φ y)
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hm : y ∈ (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i := ⟨mem_pull.2 hk, x'.P.A.left.basicOpen_le _ hi⟩
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg x'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((w.s (fun _ => k, i)).isUnit.pow l)).ge hm
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hm, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)).le h1).2⟩

theorem isLocalHom_map {σ O K : Type} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) : IsLocalHom (MvPowerSeries.map (σ := σ) f) :=
  ⟨fun a ha => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at ha ⊢
    by_contra h
    have : MvPowerSeries.constantCoeff a ∈ RingHom.ker f := hf ▸ h
    rw [MvPowerSeries.constantCoeff_map, RingHom.mem_ker.1 this] at ha
    exact not_isUnit_zero ha⟩

theorem exists_sec_cast {R : Type} [CommRing R] (x : KeyIn R) {l l' : ℕ} (h : l = l') (s : RR x l) :
    ∃ s' : RR x l', ∀ c, (show Γ(x.P.A.left, x.P.L.U c) from s'.f c) = (show Γ(x.P.A.left, x.P.L.U c) from s.f c) := by
  subst h
  exact ⟨s, fun _ => rfl⟩

theorem sub_mem_sup {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (u : Tˣ) (N : ℕ) {I : Ideal S} {J J' : Ideal T}
    (hI : I ≤ J.comap ψ) {g a : S} {G : T} (h₁ : g - a ∈ I) (h₂ : ((u⁻¹ : Tˣ) : T) ^ N * G - ψ a ∈ J') :
    G - (u : T) ^ N * ψ g ∈ J ⊔ J' := by
  have e : G - (u : T) ^ N * ψ g = (u : T) ^ N * ((((u⁻¹ : Tˣ) : T) ^ N * G - ψ a) - ψ (g - a)) := by
    have : (u : T) ^ N * ((u⁻¹ : Tˣ) : T) ^ N = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
    rw [map_sub]
    linear_combination (-G) * this
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.mem_sup_right h₂) (Ideal.mem_sup_left (hI h₁)))

end GlobalTheory.KeyKa.ClosedApprox

namespace GlobalTheory.KeyKa
open EtBaseChange ClosedApprox

theorem exists_comb_sub_mem_sup_pow : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (K : Type) [Field K] [IsAlgClosed K] (f : O →+* K) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (Y : Type) (θ : Y → (Sp (MvPowerSeries (Fin x.P.g) O) ⟶ x.P.A.left)) (c : Y → x.P.L.ι), RingHom.ker f = IsLocalRing.maximalIdeal O → 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → FinZ x s → (∀ y, θ y ≫ x.P.A.hom = spMap (algebraMap O (MvPowerSeries (Fin x.P.g) O))) → (∀ y, (∃ (V : x.P.A.left.Opens) (t : Fin x.P.g → Γ(x.P.A.left, V)), ⊤ ≤ (θ y) ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin x.P.g) O)) (θ y) V (t i) = MvPowerSeries.X i)) → (∀ y, ⊤ ≤ (θ y) ⁻¹ᵁ x.P.L.U (c y)) → Function.Injective (fun y => θ y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O))) → (∀ y i, θ y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) ∉ Out.nonzeroLocus (s i)) → ∀ (r : ℕ) (G : Y → MvPowerSeries (Fin x.P.g) K), ∃ v : Fin ((l - 0 * n) ^ x.P.g) → K, ∀ y, G y - ∑ k, v k • MvPowerSeries.map f (valT (T := (MvPowerSeries (Fin x.P.g) O)) (θ y) (x.P.L.U (c y)) ((b 0 k).f (c y))) ∈ Ideal.span (Set.range fun i => MvPowerSeries.map f (valT (T := (MvPowerSeries (Fin x.P.g) O)) (θ y) (x.P.L.U (c y)) ((s i).f (c y)))) ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r := by
  intro hL O _ _ _ K _ _ f x n l s b m Y θ c hf hn hl hb hm hZ hθ hco hc hinj hz r G
  obtain ⟨x', φ, w, hg, s', b', m', ⟨_, _, _, hp, -⟩, hs', hb', hB', hm', -, hZ'⟩ :=
    _root_.GlobalTheory.KeyBaseChangeData.exists_baseChange_data hL O K f x n l s b m hl hb hm
  replace hZ' := hZ' (inferInstanceAs (Finite (PrimeSpectrum K))) hZ
  let F : MvPowerSeries (Fin x.P.g) O →+* MvPowerSeries (Fin x.P.g) K := MvPowerSeries.map f
  have hF : IsLocalHom F := isLocalHom_map f hf
  have hw : ∀ y, (spMap F ≫ θ y) ≫ x.P.A.hom = spMap (algebraMap K (MvPowerSeries (Fin x.P.g) K)) ≫ spMap f :=
    fun y => by
      have : F.comp (algebraMap O _) = (algebraMap K (MvPowerSeries (Fin x.P.g) K)).comp f :=
        RingHom.ext fun a => MvPowerSeries.map_C f a
      rw [Category.assoc, hθ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  obtain ⟨θ', h₁, h₂⟩ : ∃ θ' : Y → (Sp (MvPowerSeries (Fin x.P.g) K) ⟶ x'.P.A.left),
      (∀ y, θ' y ≫ φ = spMap F ≫ θ y) ∧
        ∀ y, θ' y ≫ x'.P.A.hom = spMap (algebraMap K (MvPowerSeries (Fin x.P.g) K)) :=
    ⟨fun y => hp.1.lift _ _ (hw y), fun y => hp.1.lift_fst _ _ _, fun y => hp.1.lift_snd _ _ _⟩
  let P : Y → x'.P.A.left := fun y => θ' y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) K))
  have hP : ∀ y, φ (P y) = θ y (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) O)) := fun y =>
    (congrArg (fun q => q (IsLocalRing.closedPoint (MvPowerSeries (Fin x.P.g) K))) (h₁ y)).trans
      (congrArg (θ y) (IsLocalRing.comap_closedPoint F))
  have hPinj : Function.Injective P := fun y y' h => hinj ((hP y).symm.trans ((congrArg φ h).trans (hP y')))
  choose c' hc' using exists_chart x'.P.isLB
  have hU : ∀ y, ⊤ ≤ θ' y ⁻¹ᵁ x'.P.L.U (c' (P y)) := fun y => top_le_of_closedPoint _ (hc' (P y))
  have hφ : ∀ y {V : x.P.A.left.Opens}, ⊤ ≤ θ y ⁻¹ᵁ V → ⊤ ≤ (θ' y ≫ φ) ⁻¹ᵁ V := fun y V h p _ => by
    rw [h₁ y]
    exact h (show spMap F p ∈ ⊤ from trivial)
  have hval : ∀ y {V : x.P.A.left.Opens}, ⊤ ≤ θ y ⁻¹ᵁ V → ∀ a, valT (θ' y ≫ φ) V a = F (valT (θ y) V a) :=
    fun y V h a => (congrArg (fun q => valT q V a) (h₁ y)).trans (valT_spMap F (θ y) h a)
  have hW := fun y => le_inf_pull (θ' y) (c y) (c' (P y)) (hφ y (hc y)) (hU y)
  obtain ⟨u, hu⟩ : ∃ u : Y → (MvPowerSeries (Fin x.P.g) K)ˣ, ∀ y (l : ℕ) (sg : RR x l) (sg' : RR x' l),
      SecVia x' x φ w sg' sg → F (valT (θ y) (x.P.L.U (c y)) (sg.f (c y))) =
        (u y : MvPowerSeries (Fin x.P.g) K) ^ l * valT (θ' y) (x'.P.L.U (c' (P y))) (sg'.f (c' (P y))) := by
    refine ⟨fun y => Units.map (valH (θ' y) _ (hW y)).toMonoidHom (w.s (fun _ => c y, c' (P y))),
      fun y l sg sg' h => (hval y (hc y) _).symm.trans ((valT_via h (θ' y) (c y) (c' (P y)) (hφ y (hc y)) (hU y)).trans
        (congrArg (· ^ l * _) (valT_eq _ _ (hW y) _)))⟩
  choose ψ hψ using fun y z (h : P y = z) => exists_stalk_hom (θ' y) z h
  have ha : ∀ z : x'.P.A.left, ∃ a : x'.P.A.left.presheaf.stalk z, ∀ y (h : P y = z),
      (((u y)⁻¹ : (MvPowerSeries (Fin x.P.g) K)ˣ) : MvPowerSeries (Fin x.P.g) K) ^ (l - 0 * n) * G y - ψ y z h a ∈
        Ideal.span (Set.range MvPowerSeries.X) ^ r := fun z => by
    by_cases hz : ∃ y, P y = z
    · obtain ⟨y, rfl⟩ := hz
      obtain ⟨V, t, hV, ht⟩ := hco y
      obtain ⟨_, ⟨a, rfl⟩, ha⟩ := exists_mem_sub_mem_pow (ψ y _ rfl).range
        (fun a => ⟨_, (hψ y _ rfl _ (hc' _) _).symm.trans (valT_cst _ _ _ (h₂ y) _ (hU y) a)⟩)
        (fun i => ⟨_, (hψ y _ rfl (φ ⁻¹ᵁ V) (hφ y hV trivial) _).symm.trans
          ((valT_appLE (θ' y) φ le_rfl (hφ y hV) (t i)).trans ((hval y hV _).trans
            ((congrArg F (ht i)).trans (MvPowerSeries.map_X f i))))⟩) r
        ((((u y)⁻¹ : (MvPowerSeries (Fin x.P.g) K)ˣ) : MvPowerSeries (Fin x.P.g) K) ^ (l - 0 * n) * G y)
      refine ⟨a, fun y' h => ?_⟩
      obtain rfl := hPinj h
      exact ha
    · exact ⟨0, fun y h => (hz ⟨y, h⟩).elim⟩
  choose a ha using ha
  obtain ⟨sg₀, hsg₀⟩ := (GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL K x' n l s' b' m' c' hn (hg ▸ hl) hZ' hB' hm' hc').2.1 a
  obtain ⟨sg, hsg⟩ := exists_sec_cast x' (show l = l - 0 * n by simp) sg₀
  obtain ⟨v, hv, -⟩ := hB' 0 (Nat.zero_le _) sg
  have hN : (l - 0 * n) ^ x'.P.g = (l - 0 * n) ^ x.P.g := congrArg (fun r => (l - 0 * n) ^ r) hg
  refine ⟨fun k => v (k.cast hN.symm), fun y => ?_⟩
  have hzero : ∀ i, P y ∉ Out.nonzeroLocus (s' i) := fun i h =>
    hz y (i.cast hg) (hP y ▸ mem_nonzeroLocus_of_via (hs' i) _ h)
  have e : ∑ k, v (k.cast hN.symm) • F (valT (θ y) (x.P.L.U (c y)) ((b 0 k).f (c y))) =
      (u y : MvPowerSeries (Fin x.P.g) K) ^ (l - 0 * n) *
        ψ y _ rfl (gs (𝟙 _) (P y) (x'.P.L.U (c' (P y))) (sg₀.f (c' (P y)))) := by
    have e₁ := (hψ y _ rfl _ (hc' _) _).symm.trans ((congrArg (valT (θ' y) (x'.P.L.U (c' (P y))))
      ((hsg (c' (P y))).symm.trans (hv (c' (P y))))).trans ((valT_eq _ _ (hU y) _).trans (map_sum _ _ _)))
    refine Eq.trans ?_ (congrArg (_ * ·) e₁.symm)
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (finCongr hN) _ _ fun k => ?_).symm
    rw [map_mul, ← valT_eq, ← valT_eq, valT_cst _ _ _ (h₂ y) _ (hU y), mul_left_comm, Algebra.smul_def]
    exact congrArg (_ * ·) (hu y _ _ _ (hb' 0 k)).symm
  refine (congrArg (fun q => G y - q ∈ _) e).mpr (sub_mem_sup (ψ y _ rfl) (u y) _ ?_ (hsg₀ (P y) hzero) (ha _ y rfl))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine Ideal.mem_comap.2 ((Ideal.unit_mul_mem_iff_mem _ ((u y).isUnit.pow n)).1
    (Ideal.subset_span (Set.mem_range.2 ⟨i.cast hg, ?_⟩)))
  exact (hu y _ _ _ (hs' i)).trans (congrArg (_ * ·) (hψ y _ rfl _ (hc' _) _))

end GlobalTheory.KeyKa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosDApplyMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KosResidueExact

theorem kosD_apply_map {k K : Type} [CommRing k] [CommRing K] (f : k →+* K) {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k) (p q : KIx g 0 N) :
    kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0) p q =
      f (kosD (d := 0) m (fun _ => 0) p q) := by
  rcases p with p | a
  · rcases q with q | a
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [kosD, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · exact a.elim0
  · exact a.elim0

theorem descend {k K : Type} [Field k] [Field K] [Algebra k K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k)
    (H : ∀ v : KIx g 0 N → K,
      (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec w (.inl p))
    (v : KIx g 0 N → k) (hv : (kosD (d := 0) m (fun _ => 0)).mulVec v = 0) :
    ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (LinearMap.ker_eq_bot.2 (algebraMap k K).injective)
  have hl : ∀ a, lam (algebraMap k K a) = a := fun a => LinearMap.congr_fun hlam a
  obtain ⟨w, hw⟩ := H (fun p => algebraMap k K (v p)) (by
    funext p
    have := congrArg (algebraMap k K) (congrFun hv p)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this ⊢
    simpa only [kosD_apply_map] using this)
  refine ⟨fun q => lam (w q), fun p hp => ?_⟩
  have := congrArg lam (hw p hp)
  rw [hl] at this
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, kosD_apply_map]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem transport {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {g g' : ℕ} (hg : g' = g) (l n : ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin ((l - j * n) ^ g)) (Fin ((l - j' * n) ^ g)) O)
    (m' : Fin g' → ∀ j j', Matrix (Fin ((l - j * n) ^ g')) (Fin ((l - j' * n) ^ g')) K)
    (hm : ∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j'
      (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg))))
    (H : ∀ v : KIx g' 0 (fun j => (l - j * n) ^ g') → K, (kosD m' (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m' (fun _ => 0)).mulVec w (.inl p)) :
    ∀ v : KIx g 0 (fun j => (l - j * n) ^ g) → K,
      (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p) := by
  subst hg
  have : m' = fun i j j' => (m i j j').map f := by
    funext i j j'
    ext k k'
    exact hm i j j' k k'
  subst this
  exact H

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (k : Type) [Field k] (f : O →+* k) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → FinZ x s → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → k, (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p)) := by
  intro hL O _ _ _ k _ f x n l s b m hn hl hb hm hZ
  obtain ⟨x', φ, w, hg, s', b', m', -, -, -, hb', hm', hmm, hZ'⟩ :=
    _root_.GlobalTheory.KeyBaseChangeData.exists_baseChange_data hL O (AlgebraicClosure k) ((algebraMap k (AlgebraicClosure k)).comp f) x n l s b m hl hb hm
  have hfin : Finite (Sp (AlgebraicClosure k)) :=
    inferInstanceAs (Finite (PrimeSpectrum (AlgebraicClosure k)))
  have hc : ∀ y : x'.P.A.left, ∃ i, y ∈ x'.P.L.U i := fun y => exists_chart x'.P.isLB y
  choose c hc using hc
  have H := (GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL (AlgebraicClosure k) x' n l s' b' m' c hn (by rw [hg]; exact hl)
    (hZ' hfin hZ) hb' hm' hc).1
  have H' := transport ((algebraMap k (AlgebraicClosure k)).comp f) hg l n m m' hmm H
  exact descend (K := AlgebraicClosure k) (N := fun j => (l - j * n) ^ x.P.g)
    (fun i j j' => (m i j j').map f) H'

end GlobalTheory.KosResidueExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.LamOfDouble

open GlobalTheory.CechPic

theorem isIso_of_factor {X Y Z : Scheme.{0}} (y : X ⟶ Z) (j : Z ⟶ Y) [Mono j] [Flat (y ≫ j)]
    [Surjective (y ≫ j)] [QuasiCompact (y ≫ j)] : IsIso j := by
  have : IsRegularEpi (y ≫ j) := inferInstance
  have : StrongEpi (y ≫ j) := inferInstance
  have : StrongEpi j := strongEpi_of_strongEpi y j
  exact isIso_of_mono_of_strongEpi j

theorem triv_of_pull_pow (hL : Out.Laws) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB) (ha : Out.RelAmple A M) (n : ℕ) (hn : 1 ≤ n)
    (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h0 : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (h1 : ∃ t : (N.pull (((𝟙 A) ^ n : A ⟶ A) ▷ A).left).Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen := by
  have hproj : IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A M hA hM ha R (𝟙 _) A.left (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv hL.globalFns R A A hA hproj N hN
  obtain ⟨t, ht⟩ := h1
  obtain ⟨y, hy⟩ := (hH A ((𝟙 A) ^ n)).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow hL R A hA M hM ha n hn
  have e : y.left ≫ j.left = ((𝟙 A) ^ n : A ⟶ A).left := congrArg (·.left) hy
  rw [← e] at f₁ f₂ f₃
  have : IsIso j.left := isIso_of_factor y.left j.left
  have hw : inv j.left ≫ H.hom = A.hom := by rw [← Over.w j, IsIso.inv_hom_id_assoc]
  have hloc := (hH A (𝟙 A)).2 ⟨Over.homMk (inv j.left) hw, Over.OverMorphism.ext (IsIso.inv_hom_id j.left)⟩
  have key : ∃ t : (N.pull (𝟙 A ▷ A).left).Gen, t.IsGen := by
    refine GlobalTheory.exists_gen_of_local_of_section (A ⊗ A).left A.left (fst A A).left
      (lift (𝟙 A) (1 : A ⟶ A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 A) (1 : A ⟶ A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ A hA _ _ A.hom _ _
        (GlobalTheory.SeesawGlobal.isPullback_tensor A A))
      hloc ?_
    rw [← cls_eq_zero_iff (pull_isLB (pull_isLB hN _) _), cls_pull (pull_isLB hN _), cls_pull hN, ← pull_comp,
      ← Over.comp_left, id_whiskerRight, Category.comp_id]
    exact (cls_eq_zero_iff (pull_isLB hN _)).2 h0
  rw [← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, id_whiskerRight, Over.id_left, pull_id] at key
  exact (cls_eq_zero_iff hN).1 key

section Pair

variable {S : Scheme.{0}} {A T : Over S}

def ev (c : Pic (A ⊗ A).left) (x y : T ⟶ A) : Pic T.left := pull (lift x y).left c

theorem pull_ev {T' : Over S} (h : T' ⟶ T) (c : Pic (A ⊗ A).left) (x y : T ⟶ A) :
    pull h.left (ev c x y) = ev c (h ≫ x) (h ≫ y) := by
  rw [ev, ev, ← pull_comp, ← Over.comp_left, comp_lift]

variable [GrpObj A] [IsCommMonObj A]

def Biadd (c : Pic (A ⊗ A).left) : Prop :=
  ∀ (T : Over S) (x x' y : T ⟶ A), ev c (x * x') y = ev c x y + ev c x' y ∧ ev c y (x * x') = ev c y x + ev c y x'

theorem biadd_of_axes (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB)
    (ha : Out.RelAmple A M) (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h₁ : ∃ t : (N.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) : Biadd (cls N hN) := by
  intro T x x' y
  obtain ⟨a, b⟩ := GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A M hA hM ha N hN h₁ h₂ T x x' y
  rw [← cls_eq_zero_iff (LB.isLB_linComb hN _ _), cls_linComb hN] at a b
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul,
    neg_smul] at a b
  constructor
  · unfold ev
    rw [← sub_eq_zero, ← a]
    abel
  · unfold ev
    rw [← sub_eq_zero, ← b]
    abel

end Pair

theorem lam_iso_of_pull_two : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → L.IsLB → LBIso (lbPow c.diag 2) (L.pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left) → LBIso (abelian₂ c.A L) c.P := by
  intro hL h k o _ ζ R _ _ _ β c L hc hLB hiso
  have hM : c.diag.IsLB := pull_isLB c.isLB _
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hLB _ _
  have hN : (LB.div (abelian₂ c.A L) c.P).IsLB := LB.isLB_div hΛ c.isLB
  have hPow : (lbPow c.diag 2).IsLB := LB.isLB_linComb hM _ _
  set l := cls L hLB with hl
  set p := cls c.P c.isLB with hp
  have eΛ : cls _ hΛ = lam l (fst c.A c.A) (snd c.A c.A) := cls_cube_two hLB _ _ hΛ
  have eN : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) x y = lam l x y - ev p x y := by
    intro T x y
    rw [cls_div hΛ c.isLB, eΛ, ev, map_sub, pull_lam, lift_fst, lift_snd]
    rfl
  have r₁ : ev p (1 : c.A ⟶ c.A) (𝟙 c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₁
  have r₂ : ev p (𝟙 c.A) (1 : c.A ⟶ c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₂
  have n₁ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₁, lam_one_left, sub_zero]
  have n₂ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (𝟙 c.A) (1 : c.A ⟶ c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₂, lam_one_right, sub_zero]
  have bN := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ hN n₁ n₂
  have bP : Biadd p := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ c.isLB c.rig₁ c.rig₂
  have sy : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev p x y = ev p y x := by
    intro T x y
    have e : p = ev p (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    calc ev p x y = pull (lift x y).left (ev p (snd c.A c.A) (fst c.A c.A)) := by rw [← e]; rfl
      _ = ev p y x := by rw [pull_ev, lift_fst, lift_snd]
  have dbl : ∀ (T : Over (Sp R)) (x : T ⟶ c.A), pull (x * x).left l = ev p x x + ev p x x := by
    intro T x
    have e : 2 • ev p (𝟙 c.A) (𝟙 c.A) = pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left l :=
      (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hLB _)).2 hiso)
    have e' := congrArg (pull x.left) e
    rw [map_nsmul, pull_ev, ← pull_comp, ← Over.comp_left, pow_two, MonObj.comp_mul, Category.comp_id,
      two_smul] at e'
    exact e'.symm
  have z : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) (x ^ 4) y = 0 := by
    intro T x y
    have a : ev (cls _ hN) (x * x) (y * y) = 0 := by
      have o₁ : ev p (1 : T ⟶ c.A) (1 : T ⟶ c.A) = 0 := by
        have := (bP T 1 1 1).1
        rw [_root_.mul_one] at this
        exact left_eq_add.1 this
      have o₂ := dbl T 1
      rw [_root_.mul_one, o₁] at o₂
      rw [eN, lam, _root_.mul_mul_mul_comm, dbl, dbl, dbl, o₂]
      simp only [(bP T _ _ _).1, (bP T _ _ _).2, sy T y x]
      abel
    rw [show x ^ 4 = x * x * (x * x) by rw [← pow_two, ← pow_two, ← pow_mul]]
    simp only [(bN T _ _ _).1, (bN T _ _ _).2] at a ⊢
    exact a
  have fin := triv_of_pull_pow hL c.A c.ab _ hM hc.1 4 (by norm_num) _ hN n₂ (by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 (Eq.trans ?_ (z _ (fst c.A c.A) (snd c.A c.A)))
    have e : ((𝟙 c.A) ^ 4 : c.A ⟶ c.A) ▷ c.A = lift (fst c.A c.A ^ 4) (snd c.A c.A) := by
      ext
      · rw [whiskerRight_fst, lift_fst, MonObj.comp_pow, Category.comp_id]
      · rw [whiskerRight_snd, lift_snd]
    rw [e]
    rfl)
  rw [← cls_eq_zero_iff hN, cls_div hΛ c.isLB, sub_eq_zero] at fin
  exact (cls_eq_iff hΛ c.isLB).1 fin

end GlobalTheory.LamOfDouble

end
end

