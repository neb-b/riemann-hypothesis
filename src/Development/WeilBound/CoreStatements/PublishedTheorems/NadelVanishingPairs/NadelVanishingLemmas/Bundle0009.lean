module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierMapEqExtDImpEqZero
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_eq_extD_imp_eq_zero :
    ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ)
      (γ : abelian₂ K →+* abelian₂ K), IsCoord x → IsCartierMap p x γ → ∀ ζ ξ : abelian₂ K, γ ζ = extD K ξ → ζ = 0 := by
  intro K _ p _ _ n x γ hx hγ ζ ξ hζ
  obtain ⟨hli, hsp⟩ := _root_.GlobalTheory.LogDR.logWedge_basis K n x hx
  have hmem : ζ ∈ Submodule.span K (Set.range (logWedge x)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  obtain ⟨-, Q, π, -, hQ, -, hπ, hQd, -⟩ := GlobalTheory.T.cartier_projection_properties K p n x hx
  have hγs : γ (∑ I, c I • logWedge x I) = ∑ I, (c I ^ p) • logWedge x I := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => _root_.GlobalTheory.cartierMap_smul_logWedge K p n x γ hγ (c I) I
  have hfix : Q (γ (∑ I, c I • logWedge x I)) = γ (∑ I, c I • logWedge x I) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hγs, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQ, hπ]
  have h0 : ∑ I, (c I ^ p) • logWedge x I = 0 := by
    rw [← hγs, ← hfix, hζ, hQd]
  have hc : ∀ I, c I ^ p = 0 := fun I =>
    (Fintype.linearIndependent_iff.1 hli) (fun I => c I ^ p) h0 I
  have hc' : ∀ I, c I = 0 := fun I =>
    (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 (hc I)
  simp [hc']

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingFrobeniusDescent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem descend_vanishing : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G hD hG e₀ h0
  have step : ∀ e, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G (e + 1)) a) b) →
      ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e) a) b := by
    intro e he a b hab
    obtain ⟨ρ, hρ, hGe⟩ := hG e
    refine hD (G e) ρ hρ a b ?_
    rw [← hGe]
    refine DI.hypZero_of_cechZero (extD X.functionField) _ (fun x => CechDR.dDR_dDR x) ?_ ?_ (a + b) ?_
    · intro q s t _ hst
      show latSec _ _ ≤ latSec _ _
      have hle : inter 𝒜.U t ≤ inter 𝒜.U s := Finset.inf_mono hst
      intro x hx
      simp only [latSec, AddSubgroup.mem_iInf] at hx ⊢
      exact fun y hy => hx y (hle hy)
    · intro q s x hx
      have := GlobalTheory.T.log_sections_differential_closed p 𝒜 (G e) ρ hρ q (inter 𝒜.U s) x (by rw [← hGe]; exact hx)
      rw [← hGe] at this
      exact this
    · intro q b' hqb
      exact he q b' (by omega)
  induction e₀ with
  | zero => exact h0
  | succ k ih => exact ih (step k h0)

end GlobalTheory.LogDR
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LiftedStalkMapGermAppLE
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem lifted_stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens)
    (h : W' ≤ f ⁻¹ᵁ W) (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have h1 := Scheme.Hom.germ_stalkMap_apply f W z (h hz) s
  have h2 := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z hz ((f.app W).hom s)
  exact h1.trans h2.symm

theorem isLifted_of_sncCharts : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ {ι : Type} [Nonempty ι] (C : ι → SncChart g n L σ) (Z : Set X) (U : ι → X.Opens) (hU : ∀ i, U i ≤ π ⁻¹ᵁ (C i).U) (hgen : ∀ i, genericPoint X ∈ U i) (x : ι → Fin n → X.functionFieldˣ) (J : ι → Finset (Fin n)), (∀ i l, (x i l : X.functionField) = fnOf (U i) (hgen i) ((π.appLE (C i).U (U i) (hU i)).hom ((C i).t l))) → (∀ i l, l ∈ J i → ∃ c, (C i).e c = some l) → (∀ i, IsLogChart Z (U i) (x i) (J i)) → IsLifted p Z U x := by
  intro p _ Y X _ q f π hpb n s L σ hL ι _ C Z U hU hgen x J hx hJ hchart
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hη : ∀ i, π (genericPoint X) ∈ (C i).U := fun i => hU i (hgen i)
  let πK : Y.presheaf.stalk (π (genericPoint X)) →+* X.functionField := (π.stalkMap (genericPoint X)).hom
  have hflat : IsFlatLift p πK :=
    GlobalTheory.T.etale_coordinates_flat_lift p Y X q f π hpb (C i₁).U (C i₁).t (C i₁).affine (C i₁).etale (genericPoint X) (hη i₁)
  have hpK : (p : X.functionField) = 0 := by
    have h0 := (hflat.ker (p : Y.presheaf.stalk (π (genericPoint X)))).2 ⟨1, by ring⟩
    simpa using h0
  haveI : CharP X.functionField p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpK
  have hpp := logLift_pp_zero p πK hflat
  choose F hF1 hF2 hF3 using fun i =>
    GlobalTheory.T.exists_frobenius_lift_stalk p q (C i).U (C i).t (C i).affine (C i).etale (π (genericPoint X)) (hη i)

  have hlift : ∀ i l, πK ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom ((C i).t l)) =
      (x i l : X.functionField) := by
    intro i l
    rw [hx i l]
    exact lifted_stalkMap_germ_appLE π (C i).U (U i) (hU i) (genericPoint X) (hgen i) ((C i).t l)
  refine ⟨Y.presheaf.stalk (π (genericPoint X)), inferInstance, πK, F, hflat, ?_, ?_, ?_⟩
  · intro i z
    obtain ⟨w, hw⟩ := hF1 i z
    rw [hw, map_add (f := _), map_pow, map_mul, map_natCast, hpK, zero_mul, add_zero]
  · intro i l
    exact ⟨_, hlift i l, hF2 i l⟩
  intro y t hyt a ha
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨z, hz⟩ := hflat.surj (a : X.functionField)
    exact ⟨z, hz, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hsp : π (genericPoint X) ⤳ π y :=
    ((genericPoint_spec X).specializes (Set.mem_univ y)).map π.continuous
  have hsurj := (GlobalTheory.T.mod_p_squared_stalk_surjective p Y X q f π hpb y).1
  have hloc := GlobalTheory.T.local_ring_image_stalk_map π y hsp hsurj
  set At := stalkIm hsp with hAt
  have hmap : (locRing y : Set X.functionField) = (At.map πK : Set X.functionField) := by
    ext c
    rw [SetLike.mem_coe, hloc, SetLike.mem_coe, Subring.mem_map]
  have hstab : ∀ i ∈ t, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w :=
    fun i hi z hz => hF3 i (π y) (hU i (hyt i hi)) hsp z hz
  obtain ⟨u, m, hu, rfl⟩ := ((hchart i₀).logUnit y (hyt i₀ hi₀) a).1 ha
  rw [hmap]

  have hu0 : (u : X.functionField) ≠ 0 := u.ne_zero
  have hU1 : LogLift p πK F t (At.map πK : Set X.functionField) (u : X.functionField) := by
    have h2 := (unitAt_iff hu0).1 hu
    refine logLift_of_unit_mem_map p πK F t At hflat hstab _ hu0 ?_ ?_
    · exact Subring.mem_map.2 ((hloc _).1 h2.1)
    · exact Subring.mem_map.2 ((hloc _).1 h2.2)

  have hcoord : ∀ j ∈ J i₀, LogLift p πK F t (At.map πK : Set X.functionField) (x i₀ j : X.functionField) := by
    intro j hj
    obtain ⟨c, hc⟩ := hJ i₀ j hj
    refine ⟨_, hlift i₀ j, fun i hi => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.T.snc_chart_equations_differ_unit q L σ hL (C i₀) (C i) (π y) (hU i₀ (hyt i₀ hi₀)) (hU i (hyt i hi)) c
    rw [hc] at hv
    change (Y.presheaf.germ (C i₀).U (π y) (hU i₀ (hyt i₀ hi₀))).hom ((C i₀).t j) = _ at hv
    have hv' := congrArg (Y.presheaf.stalkSpecializes hsp).hom hv
    have e1 : ∀ (V : Y.Opens) (hV : π y ∈ V) (r : Γ(Y, V)),
        (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V (π y) hV).hom r) =
          (Y.presheaf.germ V (π (genericPoint X)) (hsp.mem_open V.isOpen hV)).hom r :=
      fun V hV r => TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hV hsp r
    rw [map_mul] at hv'
    have hv2 : (Y.presheaf.germ (C i₀).U (π (genericPoint X)) (hη i₀)).hom ((C i₀).t j) =
        (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) *
          (Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (((C i).e c).elim 1 (C i).t) := by
      refine (e1 _ _ _).symm.trans (hv'.trans ?_)
      congr 1
      exact e1 _ _ _
    set sv := (Y.presheaf.stalkSpecializes hsp).hom (v : Y.presheaf.stalk (π y)) with hsv
    set sv' := (Y.presheaf.stalkSpecializes hsp).hom ((v⁻¹ : (Y.presheaf.stalk (π y))ˣ) :
      Y.presheaf.stalk (π y)) with hsv'
    have hsvA : sv ∈ At := ⟨_, rfl⟩
    have hsv'A : sv' ∈ At := ⟨_, rfl⟩
    have hvv : sv * sv' = 1 := by rw [hsv, hsv', ← map_mul, Units.mul_inv, map_one]
    have hkey : ∀ o : Option (Fin n),
        F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) =
          ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom (o.elim 1 (C i).t)) ^ p := by
      rintro (_ | l)
      · show F i ((Y.presheaf.germ (C i).U (π (genericPoint X)) (hη i)).hom 1) = _
        simp
      · exact hF2 i l
    obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.frobenius_lift_unit_times_coord p At (F i) sv sv' _ hpp hsv'A hvv (hstab i hi sv hsvA) (hkey ((C i).e c))
    refine ⟨w, Subring.mem_map.2 ⟨w, hwA, rfl⟩, ?_⟩
    rw [hv2]
    exact hw
  rw [Units.val_mul, Units.coe_prod]
  refine logLift_mul p πK F t _ hflat hU1 ?_
  refine Finset.prod_induction _ (LogLift p πK F t (At.map πK : Set X.functionField))
    (fun _ _ => logLift_mul p πK F t _ hflat) (logLift_one p πK F t _) (fun j hj => ?_)
  rw [Units.val_zpow_eq_zpow_val]
  exact logLift_zpow p πK F t _ hflat (x i₀ j).ne_zero (hcoord j hj) (m j)

end GlobalTheory.DI
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogCartierRoundingFamily
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem logCartier_rounding_family : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)
    (x : Fin n → Kˣ) (J : Finset (Fin n)) (γ : abelian₂ K →+* abelian₂ K) (Y : Type) [Nonempty Y] (A : Y → Subring K)
    (t : Y → Kˣ) (r : Y → Fin n → ℕ), (∀ y, AlgChart (A y) x) → (∀ y j, r y j < p) → IsCartierMap p x γ →
    ∀ (a : ℕ) (η : abelian₂ K), (∀ y, η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) a) →
    extD K η = 0 → ∃ ζ ξ : abelian₂ K, (∀ y, ζ ∈ chartForms (A y) x J (t y) a) ∧
      (∀ y q, q + 1 = a → ξ ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (a = 0 → ξ = 0) ∧ η = γ ζ + extD K ξ := by
  intro K _ p _ _ n x J γ Y _ A t r hA hr hγ a η hη hd
  obtain ⟨y0⟩ := ‹Nonempty Y›
  have hc : IsCoord x := (hA y0).coord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h, Q, π, hhom, hQw, hπ, -, -, hstab⟩ := GlobalTheory.T.cartier_projection_properties K p n x hc
  have hT : ∀ y, (∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) (q + 1),
        h η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) 0, h η = 0) ∧
      ∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q,
        Q η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q := by
    intro y
    exact hstab (fun q => chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q)
      (GlobalTheory.T.chart_forms_differential_closed K p (A y) n x J (t y) (r y) (hA y))
      (fun i θ hθ => GlobalTheory.T.euler_contraction_chart_forms K (A y) n x J _ i θ (hA y).mem hθ)
  obtain ⟨hli, hsp⟩ := _root_.GlobalTheory.LogDR.logWedge_basis K n x hc
  obtain ⟨c, hcη⟩ : ∃ c : Finset (Fin n) → K, ∑ I, c I • logWedge x I = η :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (hsp ▸ Submodule.mem_top)
  choose g hg using fun I => hπ (c I)
  have hQη : Q η = ∑ I, g I ^ p • logWedge x I := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hcη, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQw, hg]
  refine ⟨∑ I, g I • logWedge x I, h η, ?_, ?_, ?_, ?_⟩
  · intro y
    have hm := (hT y).2.2 a η (hη y)
    rw [GlobalTheory.T.mem_chart_forms_iff] at hm
    obtain ⟨c', hc'0, hc'A, hc'eq⟩ := hm
    have heq : ∀ I, c' I = g I ^ p := by
      have h0 : ∑ I, (c' I - g I ^ p) • logWedge x I = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hc'eq, ← hQη, sub_self]
      intro I
      exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 I)
    rw [GlobalTheory.T.mem_chart_forms_iff]
    refine ⟨g, ?_, ?_, rfl⟩
    · intro I hI
      have h1 := hc'0 I hI
      rw [heq] at h1
      exact (pow_eq_zero_iff hp.ne').mp h1
    · intro I
      have h1 := hc'A I
      rw [heq] at h1
      exact _root_.GlobalTheory.LogDR.round_coeff_mem K p (A y) n x I J (t y) (r y) (g I) hp (hA y) (hr y) h1
  · intro y q hq
    subst hq
    exact (hT y).1 q η (hη y)
  · intro ha
    subst ha
    exact (hT y0).2.1 η (hη y0)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [_root_.GlobalTheory.cartierMap_smul_logWedge K p n x γ hγ]
    rw [← hQη]
    have h2 := hhom η
    rw [hd, map_zero, add_zero] at h2
    exact sub_eq_iff_eq_add'.mp h2

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsLatticeFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.log_forms_lattice_finite : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ) (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  first | exact @_root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC | exact _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC | (intros; apply _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncOpenImmersion
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_open_immersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → RelSnc (e ≫ f) d (fun i => (L i).pull e) (fun i => Cartier.secPull (σ i) e) := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_pull_of_isOpenImmersion | exact _root_.GlobalTheory.LogPair.relSnc_pull_of_isOpenImmersion | (intros; apply _root_.GlobalTheory.LogPair.relSnc_pull_of_isOpenImmersion <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncSameDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_same_divisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec), RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_of_sameDiv | exact _root_.GlobalTheory.LogPair.relSnc_of_sameDiv | (intros; apply _root_.GlobalTheory.LogPair.relSnc_of_sameDiv <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.snc_chart_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C : SncChart f d L σ), IsPullback π f' f (spMap φ) → ∃ C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π), C'.U = π ⁻¹ᵁ C.U := by
  first | exact @_root_.GlobalTheory.LogPair.sncChart_baseChange | exact _root_.GlobalTheory.LogPair.sncChart_baseChange | (intros; apply _root_.GlobalTheory.LogPair.sncChart_baseChange <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem subring_subtype_flat {k : Type} [Field k] (R : Subring k) : R.subtype.Flat := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 R.subtype_injective
  let _ := FractionRing.liftAlgebra R k
  have := FractionRing.isScalarTower_liftAlgebra R k
  have h1 : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  have h2 : Module.Flat R k := Module.Flat.trans R (FractionRing R) k
  exact (RingHom.flat_algebraMap_iff (R := R) (S := k)).2 h2

theorem resG_cstOn_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (c : R) : resG X h (cstOn p U c) = cstOn p V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫
    X.presheaf.map (homOfLE h).op).hom c = _
  erw [Scheme.Hom.appLE_map]
  rfl

theorem app_cstOn_const {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (j : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (h : V ≤ j ⁻¹ᵁ U) (c : R) :
    resG Y h ((j.app U).hom (cstOn p U c)) = cstOn (j ≫ p) V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫ j.appLE U V h).hom c = _
  exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom c)
    (Scheme.Hom.appLE_comp_appLE j p ⊤ U V le_top h)

theorem cstOn_comp_spMap_const {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}}
    (p : X ⟶ Sp R') (U : X.Opens) (c : R) : cstOn (p ≫ spMap φ) U c = cstOn p U (φ c) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p ≫ spMap φ).appLE ⊤ U le_top =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p.appLE ⊤ U le_top := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    erw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun g => g.hom c) e

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {n : ℕ}
    (c : Fin n → R) (τ : Fin n → L.Sec) : L.Sec where
  f i := ∑ a, cstOn p _ (c a) * (τ a).f i
  compat i j := by
    change resG X _ _ = _ * resG X _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_mul, resG_cstOn_const, resG_cstOn_const, mul_left_comm]
    exact congrArg _ ((τ a).compat i j)

theorem resG_comb_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X X₁ X₀ : Scheme.{0}}
    (f : X ⟶ Sp R') (f₁ : X₁ ⟶ Sp R) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁) (hf : j ≫ f₁ = f ≫ spMap φ)
    {n : ℕ} (c : Fin n → R) {U₀ : X₀.Opens} (t : Fin n → Γ(X₀, U₀)) {U₁ : X₁.Opens} {V V' W : X.Opens}
    (h₁ : U₁ ≤ π₁ ⁻¹ᵁ U₀) (hV : V ≤ j ⁻¹ᵁ U₁) (hV' : V' ≤ (j ≫ π₁) ⁻¹ᵁ U₀) (hW' : W ≤ V') (hW : W ≤ V) :
    resG X hW' (∑ a, cstOn f V' (φ (c a)) * resG X hV' (((j ≫ π₁).app U₀).hom (t a))) =
      resG X hW (resG X hV ((j.app U₁).hom
        (∑ a, cstOn f₁ U₁ (c a) * resG X₁ h₁ ((π₁.app U₀).hom (t a))))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cartier.resG_resG, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, app_cstOn_const, resG_cstOn_const, hf, cstOn_comp_spMap_const,
    Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG]
  rfl

theorem exists_finset_sec_descends : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  classical
  intro k _ R₀ X X₀ f f₀ π _ L σ hπ hL
  obtain ⟨n, c, τ, hσ⟩ := GlobalTheory.T.flat_base_change_sections R₀ k R₀.subtype X₀ X f₀ f π L (subring_subtype_flat R₀) hπ hL σ
  refine ⟨Finset.univ.image c, fun R₁ hR hF X₁ f₁ π₁ j _ hj hf => ?_⟩
  subst hj
  let c₁ : Fin n → R₁ := fun a => ⟨c a, hF (by simp)⟩
  refine ⟨secComb f₁ c₁ fun a => Cartier.secPull (τ a) π₁, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ ((j ≫ π₁) x)))
  have h1 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ (L.pull (j ≫ π₁)).U fun _ => i := (Cartier.pull_U L _ fun _ => i).ge
  have h2 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ ((L.pull π₁).pull j).U fun _ _ => i :=
    (j.preimage_mono (Cartier.pull_U L π₁ fun _ => i).ge).trans
      (Cartier.pull_U (L.pull π₁) j fun _ _ => i).ge
  refine ⟨(j ≫ π₁) ⁻¹ᵁ L.U i, fun _ => i, fun _ _ => i, h1, h2, 1, hi, ?_⟩
  refine Eq.trans ?_ (one_mul _).symm
  refine (congrArg (resG X h1) (hσ fun _ => i)).trans ?_
  exact resG_comb_pull R₁.subtype f f₁ π₁ j hf c₁ (fun a => (τ a).f i)
    (Cartier.pull_U L π₁ fun _ => i).le (Cartier.pull_U (L.pull π₁) j fun _ _ => i).le
    (Cartier.pull_U L (j ≫ π₁) fun _ => i).le h1 h2

end GlobalTheory.LogPair
end
end

