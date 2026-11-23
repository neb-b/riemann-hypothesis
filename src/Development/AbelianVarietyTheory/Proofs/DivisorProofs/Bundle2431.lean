module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem exists_bound_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Pair.shiftA (P : Pair p) (c : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => c) (fun _ => rfl), P.r, P.r', P.hr, P.hr'⟩

theorem Pair.nu_shiftA (P : Pair p) (c : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (P.shiftA c).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * c)) := by
  simp only [Pair.shiftA, Pair.nu, Pair.loc, HermLB.shift, Weight.addFn]
  have key : ∀ (n u v w : ℝ), n * Real.exp (-(u + v * (w + 2 * c)) / 2) =
      n * Real.exp (-(u + v * w) / 2) * Real.exp (-(v * c)) := by
    intro n u v w
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact key _ _ _ _

theorem Pair.nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem not_unitAt_zero (x : X) : ¬ UnitAt x (0 : X.functionField) := by
  rintro ⟨a, ha, h⟩
  exact (ha.map (algebraMap _ X.functionField)).ne_zero h

end GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_good_pair : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField), P.L = L ∧ P.Good D b s t := by
  intro hC k _ X _ p D hX L
  obtain ⟨A₀, hAmp, hNef, s₀, hs₀, hs₀ne⟩ := _root_.GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair L A₀
  have hrep := _root_.GlobalTheory.VolBr.Pair.rep_base k X p P

  obtain ⟨e, -, he_rng, he_nu, he_loc⟩ := _root_.GlobalTheory.VolBr.RepDict.rep_dict k X p P 0 1 P.A hrep.2.1
  have hsH : e s₀ ∈ P.H 0 1 := by
    show e s₀ ∈ (P.H 0 1 : Set X.functionField)
    rw [← he_rng]; exact ⟨s₀, rfl⟩
  have hη : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s₀ := (GlobalTheory.sec_ne_zero_iff s₀).1 hs₀ne
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j₀, hj₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB (genericPoint X)
  have hsne : e s₀ ≠ 0 := by
    intro h0
    have hu := (he_loc s₀ _ i₀ j₀ hi₀ hj₀).1 hη
    rw [h0] at hu
    exact not_unitAt_zero _ (by simpa [Pair.loc] using hu)
  have hs_le : ∀ σ y, P.nu 0 1 σ y (e s₀) ≤ 1 := fun σ y => by
    have h1 := he_nu s₀ σ y
    have h2 := hs₀ σ y
    have h3 := P.nu_nonneg 0 1 σ y (e s₀)
    nlinarith

  obtain ⟨S, hSfin, hS⟩ := _root_.GlobalTheory.VolBr.exists_finite_controlling_points k X p D hX P (e s₀) hsH hsne

  obtain ⟨b, hb, u, hu⟩ := _root_.GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus k X p D hX P.L.dual P.A hAmp (insert (genericPoint X) S) (hSfin.insert _)
  have hR1 : P.Rep (-1) 0 P.L.dual := by simpa using _root_.GlobalTheory.VolBr.Pair.rep_dual k X p P 1 0 P.L hrep.1
  have hR2 : P.Rep 0 b (P.A.pow b) := by simpa using _root_.GlobalTheory.VolBr.Pair.rep_pow k X p P 0 1 P.A b hrep.2.1
  have hR : P.Rep (-1) b (P.L.dual.tens (P.A.pow b)) := by
    simpa using _root_.GlobalTheory.VolBr.Pair.rep_tens k X p P (-1) 0 0 b _ _ hR1 hR2
  obtain ⟨e', -, he'_rng, he'_nu, he'_loc⟩ := _root_.GlobalTheory.VolBr.RepDict.rep_dict k X p P (-1) b _ hR
  have htH : e' u ∈ P.H (-1) b := by
    show e' u ∈ (P.H (-1) b : Set X.functionField)
    rw [← he'_rng]; exact ⟨u, rfl⟩
  have htne : e' u ≠ 0 := by
    intro h0
    have hv := (he'_loc u _ i₀ j₀ hi₀ hj₀).1 (hu (Set.mem_insert _ _))
    rw [h0] at hv
    exact not_unitAt_zero _ (by simpa [Pair.loc] using hv)
  obtain ⟨C, hC1, hCb⟩ := exists_bound_nsq hX _ u
  have ht_le : ∀ σ y, P.nu (-1) b σ y (e' u) ≤ C := fun σ y => by
    have h1 := he'_nu u σ y
    have h2 := hCb σ y
    have h3 := P.nu_nonneg (-1) b σ y (e' u)
    nlinarith

  set c := Real.log C with hc
  have hc0 : 0 ≤ c := Real.log_nonneg hC1
  have hCpos : 0 < C := by linarith
  have hexpc : Real.exp (-c) = C⁻¹ := by rw [Real.exp_neg, hc, Real.exp_log hCpos]
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hexpb : Real.exp (-((b : ℤ) * c)) ≤ C⁻¹ := by
    rw [← hexpc]; apply Real.exp_le_exp.2; push_cast; nlinarith
  refine ⟨P.shiftA c, b, e s₀, e' u, rfl, ?_⟩
  have hsub : ∀ (z x : X) (U : X.Opens), z ⤳ x → x ∈ U → z ∈ U := fun z x U h hx => h.mem_open U.isOpen hx
  exact {
    ample := hAmp
    nef := _root_.GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A c hc0 hNef
    pos := hb
    s_mem := ⟨hsH, fun σ y => by
      rw [Pair.nu_shiftA]
      have := hs_le σ y
      have h4 : Real.exp (-(((1 : ℤ) : ℝ) * c)) ≤ 1 := by
        apply Real.exp_le_one_iff.2; push_cast; linarith
      have h5 := P.nu_nonneg 0 1 σ y (e s₀)
      nlinarith [Real.exp_pos (-(((1 : ℤ) : ℝ) * c))]⟩
    s_ne := hsne
    t_mem := ⟨htH, fun σ y => by
      rw [Pair.nu_shiftA]
      have := ht_le σ y
      have h5 := P.nu_nonneg (-1) b σ y (e' u)
      calc P.nu (-1) b σ y (e' u) * Real.exp (-((b : ℤ) * c)) ≤ C * C⁻¹ :=
            mul_le_mul this hexpb (Real.exp_pos _).le hCpos.le
        _ = 1 := mul_inv_cancel₀ hCpos.ne'⟩
    t_ne := htne
    reg := fun x i j hi hj g hg h1 => hS x i j hi hj (P.loc (-1) b (e' u) i j) g (htH x i j hi hj)
      (fun z hz hzx => (he'_loc u z i j (hsub z x _ hzx hi) (hsub z x _ hzx hj)).1 (hu (Set.mem_insert_of_mem _ hz)))
      hg h1 }

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveListMSqTorsionPolarisedFibre
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.TorsList

theorem card_torsion_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {g : ℕ} {K : Type} [Field K]
    {x : Sp K ⟶ S} (hx : PolFib G L g x) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K) {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card {p : Over.mk (t ≫ x) ⟶ G // p ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨P, α, hg, h, -⟩ := hx
  subst hg
  rw [← GlobalTheory.TorsionCover.card_torsion P.A P.isAb P.smoothDim t hn]
  let Φ := GlobalTheory.ObjPull.pushEquiv h (Over.mk t)
  exact (Nat.card_congr (Φ.toEquiv.subtypeEquiv fun y => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)).symm

theorem exists_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  intro S G _ _ L g m K _ _ x hm hx
  have hpow : (m ^ 2) ^ (2 * g) = m ^ (4 * g) := by rw [← pow_mul]; congr 1; ring
  have hm2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hc : Nat.card {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} = m ^ (4 * g) := by
    have := card_torsion_comp G L hx (𝟙 (Sp K)) hm2
    rw [Category.id_comp, hpow] at this
    exact this
  have hfin : Finite {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hm0)
  let e := Finite.equivFinOfCardEq hc
  refine ⟨fun a => (e.symm a).1, fun a b hab => e.symm.injective (Subtype.ext hab), fun a => (e.symm a).2, ?_⟩
  intro K' _ _ i p hp
  have hm' : ((m ^ 2 : ℕ) : K') ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hm2
  have hc' := card_torsion_comp G L hx (spMap i) hm'
  rw [hpow] at hc'
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hepi : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  let F : {q : Over.mk x ⟶ G // q ^ (m ^ 2) = 1} → {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    fun q => ⟨preHom u q.1, by rw [← map_pow, q.2, map_one]⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h1 : spMap i ≫ a.1.left = spMap i ≫ b.1.left := congrArg (fun z => (Subtype.val z).left) hab
    exact (cancel_epi (spMap i)).1 h1
  have hfin' : Finite {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ hm0)
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hF, by rw [hc, hc']⟩).2 ⟨p, hp⟩
  refine ⟨e q, ?_⟩
  show p.left = spMap i ≫ (e.symm (e q)).1.left
  rw [Equiv.symm_apply_apply]
  exact (congrArg (fun z => (Subtype.val z).left) hq).symm

end GlobalTheory.UMin.TorsList
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantMapsAffineOpenSmoothModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_invariant_maps_of_affine_open : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R'] (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → (∀ σ, spMap (actC σ : C' →+* C') ≫ j = j ≫ act σ) → ∀ W : Y.left.Opens, IsAffineOpen W → φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ j.opensRange → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), Algebra.Smooth R O ∧ (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) := by
  intro R _ R' _ _ _ G' act Y φ hsm hpb hcomp hact C' _ _ _ _ actC j _ hj hjσ W hW h0
  obtain ⟨O, _, _, k, _, hkW, hkY, hOsm⟩ := _root_.GlobalTheory.Mum.affineChart_smooth R Y hsm W hW
  have hopen := GlobalTheory.T.thickening_preimage_eq_closedImmersion_preimage R' (maximalIdeal R') G' Y.left φ hcomp j.opensRange W h0
  have hB := fun e => _root_.GlobalTheory.Mum.ThickChart.thick_chart R' (maximalIdeal R') G' C' j hj e
  choose je hjeo hjer hjep hjeh using hB
  have hi : ∀ e, ∃ i : O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'),
      spMap (i : O →+* _) ≫ k = je e ≫ φ e := by
    intro e
    have hr : Set.range (je e ≫ φ e) ⊆ Set.range k := by
      rintro _ ⟨z, rfl⟩
      have h1 : je e z ∈ (je e).opensRange := ⟨z, rfl⟩
      rw [hjer, ← hopen, ← hkW] at h1
      exact h1
    obtain ⟨f, hf⟩ := Spec.map_surjective (IsOpenImmersion.lift k (je e ≫ φ e) hr)
    have hf' : Spec.map f ≫ k = je e ≫ φ e := by rw [hf]; exact IsOpenImmersion.lift_fac _ _ _
    have hc : CommRingCat.ofHom (algebraMap R O) ≫ f =
        CommRingCat.ofHom (algebraMap R (C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change Spec.map f ≫ spMap (algebraMap R O) = _
      rw [← hkY, ← Category.assoc, hf', Category.assoc, (hpb e).w, ← Category.assoc, hjeh]
      simp only [thick, spMap, ← Spec.map_comp]
      congr 1
      ext r
      simp [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply R R' C', Ideal.Quotient.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    refine ⟨{ f.hom with commutes' := fun r => congrArg (fun g => g.hom r) hc }, ?_⟩
    exact hf'
  choose i hi using hi
  refine ⟨O, inferInstance, inferInstance, i, hOsm, ?_, ?_, ?_⟩
  · intro e x y hxy
    have hle : (maximalIdeal R' ^ (e + 1 + 1)).map (algebraMap R' C') ≤
        (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C') :=
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
    have hsq : spMap (Ideal.Quotient.factor hle) ≫ je (e + 1) = je e ≫ thickMap R' (maximalIdeal R') e G' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, thickMap, pullback.map, pullback.lift_fst, Category.comp_id]
        rw [(hjep (e + 1)).w, (hjep e).w, ← Category.assoc]
        congr 1
        simp only [spMap, ← Spec.map_comp]
        congr 1
      · have h1 := hjeh (e + 1)
        have h2 := hjeh e
        simp only [thickObj, Over.pullback_obj_hom] at h1 h2
        simp only [Category.assoc, thickMap, pullback.map, pullback.lift_snd]
        rw [h1, ← Category.assoc, h2]
        simp only [spMap, thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext z
        simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
    have hsp : spMap (i e : O →+* _) = spMap ((Ideal.Quotient.factor hle).comp (i (e + 1) : O →+* _)) := by
      rw [← cancel_mono k, hi, ← hcomp e, ← Category.assoc, ← hsq, Category.assoc, ← hi]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hr := congrArg (fun g => g.hom x) (Spec.map_injective hsp)
    simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hr
    have hr' : i e x = Ideal.Quotient.factor hle (i (e + 1) x) := hr
    rw [hr', ← hxy, Ideal.Quotient.factor_mk]
  · intro e σ x y hxy
    obtain ⟨h, hh1, hh2⟩ := hact e σ
    have w : (je e ≫ h) ≫ pullback.fst G'.hom (thick R' (maximalIdeal R') e) =
        (spMap (Ideal.Quotient.mk ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))) ≫
          spMap (actC σ : C' →+* C')) ≫ j := by
      rw [Category.assoc, hh1, ← Category.assoc, (hjep e).w, Category.assoc, Category.assoc, hjσ]
    have hκ1 := (hjep e).lift_fst _ _ w
    have hκ2 := (hjep e).lift_snd _ _ w
    have hκi : (hjep e).lift _ _ w ≫ spMap (i e : O →+* _) = spMap (i e : O →+* _) := by
      rw [← cancel_mono k, Category.assoc, hi, ← Category.assoc, hκ1, Category.assoc, hh2]
    obtain ⟨κ', hκ'⟩ := Spec.map_surjective ((hjep e).lift _ _ w)
    rw [← hκ'] at hκ2 hκi
    simp only [spMap, ← Spec.map_comp] at hκ2 hκi
    have r1 := congrArg (fun g => g.hom y) (Spec.map_injective hκ2)
    have r2 := congrArg (fun g => g.hom x) (Spec.map_injective hκi)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at r1 r2
    have r1' : κ'.hom (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (actC σ y) := r1
    have r2' : κ'.hom (i e x) = i e x := r2
    rw [← hxy] at r2' ⊢
    rw [← r1', r2']
  · intro e
    have hpbO : IsPullback (spMap (i e : O →+* _)) (je e) k (φ e) :=
      IsOpenImmersion.isPullback _ _ _ _ (hi e).symm (by rw [hkW, hopen, hjer])
    have hp2 := hpbO.paste_vert (hpb e)
    rw [hjeh, hkY] at hp2
    have hthick : thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R') =
        spMap (algebraMap R (R' ⧸ maximalIdeal R' ^ (e + 1))) := by
      simp only [thick, spMap, ← Spec.map_comp]
      rfl
    rw [hthick] at hp2
    let b : R' ⧸ maximalIdeal R' ^ (e + 1) →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C') :=
      { Ideal.quotientMap ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C')
          Ideal.le_comap_map with
        commutes' := fun r => by
          simp [Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply R R' C']
          exact (IsScalarTower.algebraMap_apply _ _ _ _).symm }
    have hb : (Ideal.Quotient.mkₐ R ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))).comp
        (IsScalarTower.toAlgHom R R' C') = b.comp (Ideal.Quotient.mkₐ R _) := by
      ext r
      simp [b, Ideal.quotientMap_mk]
    rw [hb]
    exact _root_.GlobalTheory.Mum.tensor_of_pullback_surj_ker (maximalIdeal R' ^ (e + 1)) (i e) b hp2

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

variable {V : Type} [CommRing V] [IsDomain V]

section Data

def IsTheta (D : DegPre V) (θ : D.SecB 1 0) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : V →+* R') θ',
    IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      ThetaOne.OneBasisAt D f θ'

theorem exists_isTheta [IsLocalRing V] (hV : IsCN V) (D : DegPre V) : ∃ θ, IsTheta D θ :=
  ThetaOne.exists_theta hV D

def UnitAt [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) : Prop :=
  ∃ J, Good D.P.L (Z := Sp V) (closedPoint V) J ∧
    IsUnit (sval (Z := Sp V) θ b.left (closedPoint V) J)

def IntFrm (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) {β : TF (R := V) (FractionRing V) ⟶ D.P.A}
    (w : Frm D (FractionRing V) 1 β) (l : FractionRing V) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val

def Exhausts (P : PolAV (Sp V)) (N : ℕ) {C : Type} (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c

end Data

variable {I : Ideal V} {D : DegData V I} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G)

def Ext (x : TFK (R := V) (FractionRing V) ⟶ A.A) (h : 𝟙_ (Over (Sp V)) ⟶ G) : Prop :=
  x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) (FractionRing V)) ≫ h).left

def FrRel (w₀ : W0 U) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G)
    (l : FractionRing V) : Prop :=
  ∃ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen ∧
    ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z
          (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left)).val *
        (val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA).val =
      UT.cst (FractionRing V) z l * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG).val

def Lies (w₀ : W0 U) (g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g'.b)
    (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre (FractionRing V) k g'.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A (FractionRing V) k) (s' : Fam D.toPre (FractionRing V) k) (v : FractionRing V),
      U.ExpandsF (FractionRing V) k w₀ s s' → ValAt s x e v → SumF I (FractionRing V) (coef s' g' wk) v

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QkMul

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qk_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  intro R _ _ _ D F _ _ k d p
  refine ⟨qkMk D.tau_bimult (d • p.y) p.g ?_, rfl, rfl⟩
  rw [mul_nsmul, qk_nsmul D.tau_bimult, map_nsmul]

end GlobalTheory.Mum.QkMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QLevelRescale
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qkPt_rescale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  intro o Ω _ _ _ S ρ p _ y₀ u k k' d pk x hk hd hk' hx
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  have e : k' • pk.g = iota hB (PadicAlgCl p) (d • pk.y) := by
    rw [hk', ← smul_smul, qk_nsmul hB, map_nsmul]
  refine ⟨qkMk hB (d • pk.y) pk.g e, rfl, ?_⟩
  have L := GlobalTheory.PeriodsAnyChar.qkToAkU_level GlobalTheory.firstFiveLaws u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p)
    k d k' hk hd (by rw [hk', Nat.mul_comm]) pk (qkMk hB (d • pk.y) pk.g e) x
  exact (L.1 rfl rfl).1 hx

end GlobalTheory.QLevelRescale
end
end

