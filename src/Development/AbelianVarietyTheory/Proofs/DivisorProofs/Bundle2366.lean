module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem formOrd_append_of_ord_eq : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = (fun ω => @dite ℤ (∃ a, P0.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (fun i => (x i : K))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x P P0 hE hx hP hP0 hord
  have hιinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hE.retr, hE.retr] at this
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  have hginj : Function.Injective (T.subtype.comp ι) := Subtype.val_injective.comp hιinj
  let j : K →+* L := IsFractionRing.lift hginj
  have hj : ∀ g : R, j (g : K) = (ι g : L) := fun g => IsFractionRing.lift_algebraMap hginj g
  have hordK : ∀ f : K, f ≠ 0 → P.ord (j f) = P0.ord f := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac f
    have ha0 : a ≠ 0 := by rw [← e]; exact mul_ne_zero hf hb0
    have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
    have hjb : j b ≠ 0 := (map_ne_zero j).2 hb0
    have hja : j a ≠ 0 := (map_ne_zero j).2 ha0
    have hga : (⟨a, ha⟩ : R) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have hgb : (⟨b, hb⟩ : R) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have h1 := hord _ hga
    have h2 := hord _ hgb
    rw [← hj] at h1 h2
    rw [ef, map_mul, map_inv₀, P.ord_mul hja (inv_ne_zero hjb), P.ord_inv,
      P0.ord_mul ha0 (inv_ne_zero hb0), P0.ord_inv]
    simp only at h1 h2
    rw [h1, h2]
  have hA : ∀ f ∈ P0.ring, j f ∈ P.ring := by
    intro f hf
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact P.ring.zero_mem
    · have hj0 : j f ≠ 0 := (map_ne_zero j).2 h0
      rw [← P.ord_nonneg_iff hj0, hordK f h0, P0.ord_nonneg_iff h0]
      exact hf
  have hτ : ∀ i, (τ i : L) ∈ P.ring := fun i => hP.1 _ (τ i).2
  let ρ : P0.ring →+* P.ring := j.restrict P0.ring P.ring hA
  let τ' : Fin r → P.ring := fun i => ⟨τ i, hτ i⟩
  have hc : ρ.comp P0.const = P.const := by
    ext a
    change j (cK a) = cL a
    have := hj ⟨cK a, hE.base.const_mem a⟩
    rw [hE.const a] at this
    exact this
  have hFE := GlobalTheory.T.formallyEtale_polynomialPlace_to_place cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ

  letI := P0.const.toAlgebra
  letI := cK.toAlgebra
  haveI : IsScalarTower ℂ P0.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ P0.ring := P0.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ P0.ring
  obtain ⟨t0, ht0⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht0
  have h1 := trdeg_eq_of_basis_kaehler ℂ K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  have hω0 : IsFreeGen P0.ring (dForm P0.const z) := isFreeGen_dForm z b hb
  have hF : IsFreeGen P.ring (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) :=
    _root_.GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial P0.const P.const ρ hc z b hb τ' hFE
  haveI : Algebra.FormallyEtale P0.ring K := .of_isLocalization (nonZeroDivisors P0.ring)
  let bK : Module.Basis (Fin (m + 1)) K (Omega cK) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ P0.ring K).basis b
  have hbK : ∀ i, bK i = dFun cK (z i : K) := by
    intro i
    simp only [bK, IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D ℂ ℂ P0.ring K (z i)
  have hrat0 : P0.toRat (m + 1) (dForm P0.const z) = dForm cK (fun i => (z i : K)) :=
    formMap_dForm _ rfl z
  have hratP : P.toRat (r + (m + 1)) (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) =
      dForm cL (Fin.append (fun i => (τ i : L)) (fun i => j (z i : K))) := by
    refine (formMap_dForm _ rfl _).trans (congrArg _ (funext fun k => ?_))
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]; rfl
    · simp only [Fin.append_right]; rfl
  obtain ⟨f, hf⟩ := (P0.isFreeGen_toRat hω0).2 (dForm cK (fun i => (x i : K)))
  simp only at hf
  have hxK := isFreeGen_dForm_of_trBasis cK hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hf
    exact one_ne_zero (hxK.1 (a₁ := 1) (a₂ := 0) (by simp [← hf]))
  have hK : P0.formOrd (dForm cK (fun i => (x i : K))) = P0.ord f := by
    rw [← hf]; exact P0.formOrd_smul_toRat hω0 hf0
  have key := _root_.GlobalTheory.TopFormAppend.dForm_append_eq_smul cK cL j (RingHom.ext fun a => by
      change j (cK a) = cL a
      have := hj ⟨cK a, hE.base.const_mem a⟩
      rw [hE.const a] at this
      exact this) (fun i => (x i : K)) (fun i => (z i : K)) bK hbK f
    (by rw [← hf, hrat0]) (fun i => (τ i : L))
  have e1 : (fun i => j (x i : K)) = fun i => (ι (x i) : L) := funext fun i => hj (x i)
  rw [e1, ← hratP] at key
  change P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) =
    P0.formOrd (dForm cK (fun i => (x i : K)))
  rw [key, P.formOrd_smul_toRat hF ((map_ne_zero j).2 hf0), hordK f hf0, hK]

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSums
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SepLam

theorem mem_of_forall_mem_sup_pow {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (I : Ideal V) (hI : I ≠ ⊤)
    (z : V) (h : ∀ j : ℕ, z ∈ I ⊔ maximalIdeal V ^ j) : z ∈ I := by
  haveI : Nontrivial (V ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (V ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal V).map (Ideal.Quotient.mk I) ≤ maximalIdeal (V ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr fun x hx hu => hx (isUnit_of_map_unit (Ideal.Quotient.mk I) x hu)
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (V ⧸ I)) (Ideal.IsMaximal.ne_top inferInstance)
  have hz : Ideal.Quotient.mk I z ∈ ⨅ j : ℕ, maximalIdeal (V ⧸ I) ^ j := by
    refine Ideal.mem_iInf.mpr fun j => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h j)
    rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    refine pow_le_pow_left' hmax j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact hz

end GlobalTheory.Poinc.SepLam

namespace GlobalTheory.Poinc.SepLam

theorem lam_of_exact : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 1 ≤ s → 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ := by
  intro O _ bar q s W A _ _ Φ N₁ hs hN hE
  classical
  refine ⟨(W ⟨0, hs⟩ ⟨0, hs⟩).toNat, fun y hm i x hx => ?_⟩
  haveI : Subsingleton (Fin (Φ.m y)) := by rw [hm]; infer_instance
  have hsym : ∀ a b, Φ.δ y i a b = Φ.δ y i b a := (Φ.bal y i).1
  have hδpos : ∀ z, z ≠ 0 → 0 < Φ.δ y i z z := fun z hz => by
    obtain ⟨k, hk⟩ := Φ.pos y z hz
    rwa [Subsingleton.elim k i] at hk
  obtain ⟨c0, hc0, hge⟩ := QWDom.qW_ge s W Φ.posW
  have hqpos : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → 0 < qW W (Φ.δ y i) mu := by
    intro mu hmu
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hmu
    have h1 : Φ.δ y i (mu v) (mu v) ≤ ∑ u, Φ.δ y i (mu u) (mu u) :=
      Finset.single_le_sum (f := fun u => Φ.δ y i (mu u) (mu u)) (fun u _ => Φ.nonneg y i _) (Finset.mem_univ v)
    have h2 : (0 : ℝ) < c0 * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) :=
      mul_pos hc0 (by exact_mod_cast (hδpos _ hv).trans_le h1)
    have h3 := hge (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) mu
    exact_mod_cast h2.trans_le h3
  have hqnn : ∀ mu : Fin s → Φ.X y, 0 ≤ qW W (Φ.δ y i) mu := fun mu =>
    GlobalTheory.Poinc.qW_nonneg Φ.posW hsym (Φ.nonneg y i) mu

  have hsne : (Pi.single ⟨0, hs⟩ x : Fin s → Φ.X y) ≠ 0 := fun h0 => hx (by simpa using congrFun h0 ⟨0, hs⟩)
  have hP : ∃ n : ℕ, ∃ mu : Fin s → Φ.X y, mu ≠ 0 ∧ (qW W (Φ.δ y i) mu).toNat = n :=
    ⟨_, Pi.single ⟨0, hs⟩ x, hsne, rfl⟩
  obtain ⟨mu₀, hmu₀, hq₀⟩ := Nat.find_spec hP
  have hmin : ∀ mu : Fin s → Φ.X y, mu ≠ 0 → qW W (Φ.δ y i) mu₀ ≤ qW W (Φ.δ y i) mu := by
    intro mu hmu
    have h1 := Nat.find_min' hP ⟨mu, hmu, rfl⟩
    rw [← hq₀] at h1
    have := hqnn mu₀
    have := hqnn mu
    omega
  have hlead : ∀ nu : Fin s → Φ.X y, nu ≠ 0 → qW W (Φ.δ y i) mu₀ < qW W (Φ.δ y i) (mu₀ + N₁ • nu) :=
    fun nu hnu => _root_.GlobalTheory.Poinc.LeastVec.least_lt_add_smul s W Φ.posW (Φ.X y) (Φ.δ y i) hsym (Φ.nonneg y i) ⊤ (fun mu _ h => hqpos mu h)
      mu₀ trivial hmu₀ (fun mu _ h => hmin mu h) N₁ hN nu trivial hnu
  set n₀ := (qW W (Φ.δ y i) mu₀).toNat with hn₀
  have hn₀z : (n₀ : ℤ) = qW W (Φ.δ y i) mu₀ := Int.toNat_of_nonneg (hqnn mu₀)
  have hn₀pos : 1 ≤ n₀ := by have := hqpos mu₀ hmu₀; omega
  have hmono : ∀ mu : Fin s → Φ.X y, mono W (Φ.t y) (Φ.δ y) mu = Φ.t y i ^ (qW W (Φ.δ y i) mu).toNat := by
    intro mu
    rw [mono, Fintype.prod_subsingleton _ i]
  have hsum : ∀ mu : Fin s → Φ.X y, ∑ k, qW W (Φ.δ y k) mu = qW W (Φ.δ y i) mu := fun mu =>
    Fintype.sum_subsingleton _ i
  obtain ⟨c, hc⟩ := Φ.u_unit y mu₀
  obtain ⟨h, hh⟩ := hE y mu₀ c
  have htm := (Φ.t_mem y i).1
  have hI : Ideal.span {Φ.t y i ^ (n₀ + 1)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_mem_of_mem _ htm _ (Nat.succ_pos _)) hu
  have key : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ ∈ Ideal.span {Φ.t y i ^ (n₀ + 1)} := by
    haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
    refine mem_of_forall_mem_sup_pow _ hI _ fun j => ?_
    obtain ⟨S, hS1, hS2, hS3⟩ := hh (max j (n₀ + 1))
    have hmem : mu₀ ∈ S := by
      by_contra hn
      have := hS2 mu₀ (fun v => ⟨0, by simp⟩) hn
      rw [hsum] at this
      omega
    have hsplit : Φ.ev y h - Φ.u y mu₀ c * Φ.t y i ^ n₀ =
        ∑ mu ∈ S.erase mu₀, Φ.term y mu c + (Φ.ev y h - RingHom.id _ (∑ mu ∈ S, Φ.term y mu c)) := by
      rw [← Finset.add_sum_erase S _ hmem, VPre.term, hmono, RingHom.id_apply]
      ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun mu hmu => ?_)
      (Ideal.pow_le_pow_right (le_max_left j (n₀ + 1)) hS3)
    obtain ⟨hne, hmuS⟩ := Finset.mem_erase.mp hmu
    have hcong := hS1 mu hmuS
    set nu : Fin s → Φ.X y := fun v => (hcong v).choose
    have hmu_eq : mu = mu₀ + N₁ • nu := funext fun v => (hcong v).choose_spec
    have hnu : nu ≠ 0 := by
      rintro h0
      rw [h0, smul_zero, add_zero] at hmu_eq
      exact hne hmu_eq
    have hlt := hlead nu hnu
    rw [← hmu_eq] at hlt
    rw [VPre.term, hmono, Ideal.mem_span_singleton]
    refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
    have := hqnn mu
    omega
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp key
  have hev : Φ.ev y h = Φ.t y i ^ n₀ * (Φ.u y mu₀ c + r * Φ.t y i) := by linear_combination -hr
  have hunit : IsUnit (Φ.u y mu₀ c + r * Φ.t y i) := by
    by_contra hu
    have h1 : Φ.u y mu₀ c + r * Φ.t y i ∈ maximalIdeal (Φ.V y) := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have h2 := (maximalIdeal (Φ.V y)).sub_mem h1 ((maximalIdeal (Φ.V y)).mul_mem_left r htm)
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hc
  have hevm : Φ.ev y h ∈ maximalIdeal (Φ.V y) := by
    rw [hev]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ htm _ hn₀pos)
  refine ⟨h, ?_, ?_⟩
  · by_contra hA
    have hu : IsUnit h := by
      by_contra hu'
      exact hA ((IsLocalRing.mem_maximalIdeal _).mpr hu')
    exact (IsLocalRing.mem_maximalIdeal _).mp hevm (hu.map (Φ.ev y))
  · have hd : Φ.ev y h ∣ Φ.t y i ^ n₀ := by
      rw [hev]
      exact (hunit.mul_right_dvd).mpr dvd_rfl
    refine hd.trans (pow_dvd_pow _ ?_)
    have hsingle : qW W (Φ.δ y i) (Pi.single ⟨0, hs⟩ x) = W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x := by
      simp only [qW]
      rw [Finset.sum_eq_single ⟨0, hs⟩ (fun u _ hu => Finset.sum_eq_zero fun v _ => by
          simp [Pi.single_eq_of_ne hu]) (by simp),
        Finset.sum_eq_single ⟨0, hs⟩ (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
      simp
    have hle := hmin _ hsne
    rw [hsingle] at hle
    have hdx := hδpos x hx
    have hW : 0 < W ⟨0, hs⟩ ⟨0, hs⟩ := by
      by_contra hW
      push_neg at hW
      have : W ⟨0, hs⟩ ⟨0, hs⟩ * Φ.δ y i x x ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hW hdx.le
      omega
    zify
    rw [Int.toNat_of_nonneg hW.le, Int.toNat_of_nonneg hdx.le, hn₀z]
    exact hle

end GlobalTheory.Poinc.SepLam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.Mum.GenDesc

theorem fracMap_finite : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  intro R R' _ _ _ _ ρ hρ hfin
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  have hinj : Function.Injective (algebraMap R R') := hρ
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  letI : Algebra (FractionRing R) (FractionRing R') := FractionRing.liftAlgebra R (FractionRing R')
  haveI : IsScalarTower R (FractionRing R) (FractionRing R') :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing R')
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R)) (FractionRing R') :=
    inferInstance
  haveI : Module.Finite (FractionRing R) (FractionRing R') :=
    Module.Finite.of_isLocalization R R' (nonZeroDivisors R)
  have heq : fracMap ρ hρ = algebraMap (FractionRing R) (FractionRing R') := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    rw [fracMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' (FractionRing R')]
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem frobKerIdeal_le_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) ≤ kerIdeal ((relFrob h G).app n) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : counit (R := R) a = 0 := ha
  have hb : (frobProj h G).app n a ∈ augIdeal R ((frobTwist h G).A n) := by
    change counit (R := R) ((frobProj h G).app n a) = 0
    exact (SemiBialgHom.counit_map ((frobProj h G).app n) a).trans
      ((congrArg (frobRing h) ha').trans (map_zero (frobRing h)))
  change a ^ p ∈ kerIdeal ((relFrob h G).app n)
  rw [← relFrob_app_frobProj h n a]
  exact Ideal.mem_map_of_mem ((relFrob h G).app n).toAlgHom hb

theorem frobKerIdeal_eq_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) :=
  le_antisymm (frobKerIdeal_le_kerIdeal_relFrob p R h G n)
    (kerIdeal_relFrob_le_frobKerIdeal p R h G n)

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstGenericAppInjective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fst_generic_app_injective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (W : X.Opens) : Function.Injective ((pullback.fst p (jK R)).app W).hom := by
  have : IsDominant (jK R) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p (jK R)).flip
  exact (pullback.fst p (jK R)).app_injective W

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf} {X₁ : USetup C}

def UDeep.GalLab (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisBaseChangeSemiAbelianInvariantUnitsDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvUnit

theorem exists_unit_of_mem_range {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (u : Bˣ) (h : u.val ∈ Set.range f) (h' : (u⁻¹).val ∈ Set.range f) : ∃ g : Aˣ, Units.map (f : A →* B) g = u := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  have e : g * g' = 1 := hf (by rw [map_mul, hg, hg', map_one, Units.mul_inv])
  exact ⟨⟨g, g', e, (mul_comm g' g).trans e⟩, Units.ext hg⟩

theorem map_inv_eq {B : Type} [CommRing B] (t : B →+* B) (u : Bˣ) (h : t u.val = u.val) :
    t (u⁻¹).val = (u⁻¹).val := by
  have e : u.val * t (u⁻¹).val = 1 := by
    conv_lhs => rw [← h]
    rw [← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem invariant_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  intro R _ _ _ _ R' _ _ _ ρ hF hG G' _ G _ _ β act hS hβ hact hinv O
  have := hS.smooth
  have H := _root_.GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hF hG G.left G'.left G.hom G'.hom β inferInstance hβ.1 act hinv
    (fun σ => (hact σ).1.w) O
  refine ⟨H.1, fun u hu => ?_⟩
  exact exists_unit_of_mem_range (β.app O).hom H.1 u (H.2 _ hu) (H.2 _ fun σ h => map_inv_eq _ u (hu σ h))

end GlobalTheory.Mum.InvUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_inf_of_separated_over_affineOpen : ∀ {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h] (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens), Ω₁.1 ≤ h ⁻¹ᵁ U.1 → Ω₂.1 ≤ h ⁻¹ᵁ U.1 → IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  first | exact @GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage | exact GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage | (intros; apply GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage <;> assumption)
end

