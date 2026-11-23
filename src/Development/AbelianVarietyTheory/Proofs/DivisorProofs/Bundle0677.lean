module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LaurentNoeth

def lmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : S →+* LaurentPolynomial S).comp f) (laurentVarUnit S)

theorem laurentVarUnit_zpow (S : Type) [CommRing S] (n : ℤ) :
    ((laurentVarUnit S ^ n : (LaurentPolynomial S)ˣ) : LaurentPolynomial S) = LaurentPolynomial.T n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]; rfl
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, sub_eq_add_neg, LaurentPolynomial.T_add]; rfl

theorem laurentMap_C_mul_T {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (n : ℤ) :
    lmap f (LaurentPolynomial.C a * LaurentPolynomial.T n) = LaurentPolynomial.C (f a) * LaurentPolynomial.T n := by
  simp [lmap, laurentVarUnit_zpow]

theorem lext {R : Type} [CommRing R] {p p' : LaurentPolynomial R} (h : ∀ n, p.coeff n = p'.coeff n) : p = p' :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

theorem lmap_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (lmap f p).coeff n = f (p.coeff n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq,
      map_add]
  | C_mul_T k a =>
    rw [laurentMap_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

theorem lmap_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lmap f) := by
  intro p p' h
  refine lext fun n => ?_
  apply hf
  rw [← lmap_apply, ← lmap_apply, h]

theorem lmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    lmap (g.comp f) = (lmap g).comp (lmap f) := by
  refine RingHom.ext fun p => lext fun n => ?_
  rw [RingHom.comp_apply, lmap_apply, lmap_apply, lmap_apply, RingHom.comp_apply]

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (F : R →+* S) (G : S →+* T) :
    spMap (G.comp F) = spMap G ≫ spMap F := by
  show sch.map (Spec.map (CommRingCat.ofHom (G.comp F))) = sch.map (Spec.map (CommRingCat.ofHom G)) ≫ sch.map (Spec.map (CommRingCat.ofHom F))
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

attribute [local instance] Classical.propDecidable

variable {A : Type} [CommRing A]

def sub (u : A) (s : Finset A) : Subalgebra ℤ A := Algebra.adjoin ℤ (↑(insert u s) : Set A)

theorem sub_mono (u : A) : Monotone (sub u) := fun _ _ h =>
  Algebra.adjoin_mono (Finset.coe_subset.2 (Finset.insert_subset_insert u h))

theorem mem_sub (u : A) (s : Finset A) {a : A} (ha : a ∈ insert u s) : a ∈ sub u s :=
  Algebra.subset_adjoin (Finset.mem_coe.2 ha)

theorem lmap_val_comp (u : A) {s t : Finset A} (hst : s ≤ t) :
    (lmap (sub u t).val.toRingHom).comp (lmap (Subalgebra.inclusion (sub_mono u hst)).toRingHom) =
      lmap (sub u s).val.toRingHom := by
  rw [← lmap_comp]; rfl

def diag (u : A) : Finset A ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (LaurentPolynomial (sub u s))
  map {s t} h := CommRingCat.ofHom (lmap (Subalgebra.inclusion (sub_mono u (leOfHom h))).toRingHom)
  map_id s := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply, lmap_apply]; rfl)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun p => lext fun n => by
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, lmap_apply]; rfl)

def cocone (u : A) : Cocone (diag u) where
  pt := CommRingCat.of (LaurentPolynomial A)
  ι := { app := fun s => CommRingCat.ofHom (lmap (sub u s).val.toRingHom)
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact CommRingCat.hom_ext (lmap_val_comp u (leOfHom h)) }

theorem exists_preimage (u : A) (x : LaurentPolynomial A) : ∃ s y, lmap (sub u s).val.toRingHom y = x := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨s, y, rfl⟩ := hp
    obtain ⟨t, z, rfl⟩ := hq
    refine ⟨s ∪ t, lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_left)).toRingHom y +
      lmap (Subalgebra.inclusion (sub_mono u Finset.subset_union_right)).toRingHom z, ?_⟩
    rw [map_add (f := _), ← RingHom.comp_apply, ← RingHom.comp_apply, ← lmap_comp, ← lmap_comp]
    rfl
  | C_mul_T k a =>
    refine ⟨{a}, LaurentPolynomial.C ⟨a, mem_sub u _ (by simp)⟩ * LaurentPolynomial.T k, ?_⟩
    rw [laurentMap_C_mul_T]
    rfl

theorem cocone_isColimit (u : A) : Nonempty (IsColimit (cocone u)) := by
  haveI : ReflectsColimitsOfShape (Finset A) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change LaurentPolynomial A at x
    obtain ⟨s, y, hy⟩ := exists_preimage u x
    exact ⟨s, y, hy.symm⟩
  · intro s t xs xt h
    refine ⟨s ∪ t, homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, ?_⟩
    apply lmap_injective (sub u (s ∪ t)).val.toRingHom (fun a b hab => Subtype.ext hab)
    · change (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xs = (lmap (sub u (s ∪ t)).val.toRingHom).comp (lmap _) xt
      rw [← lmap_comp, ← lmap_comp]
      exact h

theorem sub_fg (u : A) (s : Finset A) : (sub u s).FG := ⟨insert u s, rfl⟩

end GlobalTheory.EtC.LaurentNoeth


open GlobalTheory.EtC.LaurentNoeth in
theorem GlobalTheory.EtC.laurent_vanishing_of_noetherian : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  classical
  intro q _ hN A _ hA hq n i hn
  refine ⟨fun x y => ?_⟩
  suffices key : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 by rw [key x, key y]
  intro x
  set u : A := ((hq.unit⁻¹ : Aˣ) : A)
  obtain ⟨hc⟩ := cocone_isColimit u
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    have := hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A); simpa using this
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag u) (cocone u) hc n i).1 x hqL
  haveI : Algebra.FiniteType ℤ (sub u j) := (Subalgebra.fg_iff_finiteType _).1 (sub_fg u j)
  haveI : IsNoetherianRing (sub u j) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨C, _, hCn, hCsh, f, g, hfg⟩ := GlobalTheory.T.exists_noetherian_sh_factorization (sub u j) A hA (sub u j).val.toRingHom
  haveI := hCn
  have hqS : IsUnit (q : sub u j) := by
    refine isUnit_iff_exists_inv.2 ⟨⟨u, mem_sub u j (Finset.mem_insert_self u j)⟩, ?_⟩
    apply Subtype.ext
    simp [u]
  have hqC : IsUnit (q : C) := by have := hqS.map f; simpa using this
  haveI := hN C hCsh hqC n i hn
  have e : (cocone u).ι.app j = CommRingCat.ofHom ((lmap g).comp (lmap f)) := by
    rw [← lmap_comp, hfg]; rfl
  rw [← hy, e]
  change pull _ (spMap ((lmap g).comp (lmap f))) _ _ y = 0
  rw [spMap_comp']
  refine (pull_comp (ZMod q) (spMap (lmap g)) (spMap (lmap f)) (tw q i) n y).trans ?_
  have : pull _ (spMap (lmap f)) (tw q i) n y = 0 := Subsingleton.elim _ _
  rw [this, map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralWeightedAtlasFrameEtaleTransfer
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lintegral_frame_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E U z β hE hβ a w ha hw hw0
  classical
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hc := api_nsq_contOn A hE.isOpen hβ.1
  have hm := ContinuousOn.measurable_piecewise hc
    (continuousOn_const (c := (0 : ℝ)) (s := Uᶜ)) hUm
  set N : Y → ℝ := U.piecewise (A.nsq (A.kap + E) β) (fun _ => 0) with hN
  have hNU : ∀ y ∈ U, N y = A.nsq (A.kap + E) β y := fun y hy => by simp [hN, hy]
  have hΦ : Measurable fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y) :=
    ENNReal.measurable_ofReal.comp ((hm.mul (ha.norm.pow_const 2)).mul hw)
  rw [setLIntegral_congr_fun hUm
    (g := fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y)) (fun y hy => by simp only [hNU y hy]),
    _root_.GlobalTheory.EtaleMeasure.lintegral_mu_etale n Y ι La A U z hE _ hΦ]
  refine lintegral_congr fun x => ?_
  have hJ : 0 < A.nsq A.kap (jdet A z) x := by
    have := hE.det_ne (A.pick (x : Y)) x x.2 (A.mem_pick _)
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hB : 0 < A.nsq (A.kap + E) β x := by
    have : β (A.pick (x : Y)) x ≠ 0 := by
      exact hβ.2 _ x.2
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hwx := hw0 x x.2
  rw [hNU x x.2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold GlobalTheory.OTY.TwEst.wt
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_neg, Real.exp_log hB, Real.exp_log hJ]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinPadicValPowSubOneCoprimeEqClosedFormula
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.MinValClosed

theorem mE_le_padicValNat {l n a : ℕ} (hl : l.Prime) (hn : 2 ≤ n) (he : Even n) (ha : 2 ≤ a)
    (hac : a.Coprime l) : Formalism.PairingDivisionLocalBalance.mE l n ≤ padicValNat l (a ^ n - 1) := by
  haveI := Fact.mk hl
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h2 hd
  · subst h2
    have hodd : ¬ 2 ∣ a := by
      intro h
      have := Nat.Coprime.coprime_dvd_left h hac
      norm_num at this
    have ha1 : 1 < a := by omega
    have := padicValNat.pow_two_sub_one_ge ha1 hodd (by omega) he
    simp only [← Nat.padicValNat_def] at this
    omega
  · obtain ⟨k, rfl⟩ := hd
    have hl3 : 3 ≤ l := by have := hl.two_le; omega
    have hk : k ≠ 0 := by rintro rfl; simp at hn
    have hodd : Odd l := hl.odd_of_ne_two h2
    set b := a ^ (l - 1) with hb
    have hb1 : 1 < b := Nat.one_lt_pow (by omega) (by omega)
    have hfer : l ∣ b - 1 := by
      have := Nat.ModEq.pow_card_sub_one_eq_one hl hac
      exact (Nat.modEq_iff_dvd' hb1.le).mp this.symm
    have hnd : ¬ l ∣ b := by
      intro h
      have h1 : l ∣ a := hl.dvd_of_dvd_pow h
      have : l ∣ Nat.gcd a l := Nat.dvd_gcd h1 dvd_rfl
      rw [hac] at this
      exact hl.one_lt.ne' (Nat.dvd_one.mp this)
    have hpow : a ^ ((l - 1) * k) - 1 = b ^ k - 1 ^ k := by rw [pow_mul, one_pow]
    rw [hpow]
    have hval := padicValNat.pow_sub_pow hodd hb1 (by simpa using hfer) hnd hk
    simp only [← Nat.padicValNat_def] at hval
    rw [hval]
    have hv1 : 1 ≤ padicValNat l (b - 1) := by
      rw [Nat.padicValNat_def]
      exact one_le_multiplicity_of_dvd (by omega) hfer
    have hvl : padicValNat l (l - 1) = 0 := by
      rw [Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) hk, hvl]
    omega
  · exact Nat.zero_le _

theorem mMin_eq_mE : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  intro hmv l n hl hn he
  apply le_antisymm
  · obtain ⟨a, ha, hac, hv⟩ := hmv l n hl hn he
    exact Nat.sInf_le ⟨a, ha, hac, hv.symm⟩
  · obtain ⟨a, ha, hac, hv⟩ := mMin_mem hl.one_lt.le n
    rw [hv]
    exact mE_le_padicValNat hl hn he ha hac

end GlobalTheory.MinValClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeZeroOfDvd
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.RedCoef

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

def semiId (I : Cx S) : SemiMap I I where
  app _ _ := AddMonoidHom.id _
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

def semiComp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map (K.d s t) (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map (I.d s t) a))
    rw [σ.comm, ρ.comm]

theorem semiId_op (I : Cx S) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (semiId I).op.app E n x = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S S (semiId I)).2 E n α α (fun _ _ _ _ _ => rfl)

theorem semiComp_op {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (semiComp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).1 E n β
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).2 E n β γ hγ]
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S T (semiComp ρ σ)).2 E n α γ (fun p s h U y => by
    rw [hγ p s h U y, hβ p s h U y]; rfl)

theorem neZero_of_dvd {q Q : ℕ} [NeZero Q] (h : q ∣ Q) : NeZero q :=
  ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp h)⟩

theorem div_mul_div {Q q r : ℕ} [NeZero Q] (hq : q ∣ Q) (hr : r ∣ q) : Q / q * (q / r) = Q / r := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨l, rfl⟩ := hr
  have hQ := NeZero.ne (r * l * k)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hQ
  have hl0 : l ≠ 0 := by rintro rfl; simp at hQ
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hr0 hl0)),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0), mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0),
    mul_comm]

end GlobalTheory.EtC.RedCoef

namespace GlobalTheory.EtC.RedCoef

theorem a11 : GlobalTheory.EtC.A11 := by
  intro Q q _ hqQ E
  haveI : NeZero q := neZero_of_dvd hqQ
  refine ⟨fun a b => _root_.GlobalTheory.EtC.RedCup.reduction_cup Q q hqQ E a b, fun hE => ⟨GlobalTheory.T.tateTwistCoefficientReduction_unitClass Q q hqQ E hE, fun L => GlobalTheory.T.red_c1_eq_c1_of_dvd Q q hqQ E hE L⟩,
    fun n i a => ?_, fun r hr n i a => ?_⟩
  · have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (redMap Q Q i).app U 0 (resGen i ζ) = (semiId (res _ (tw Q i))).app U 0 (resGen i ζ) := by
      intro U ζ
      refine GlobalTheory.T.tateTwistReductionResolutionMap_generator Q Q dvd_rfl i U ζ ζ ?_
      rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne Q)), pow_one]
    exact (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q Q dvd_rfl i _ _ hgen E n a).trans (semiId_op _ E n a)
  · haveI : NeZero r := neZero_of_dvd hr
    have hrQ : r ∣ Q := hr.trans hqQ
    have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (semiComp (redMap Q q i) (redMap q r i)).app U 0 (resGen i ζ) = (redMap Q r i).app U 0 (resGen i ζ) := by
      intro U ζ
      obtain ⟨η, hη⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.2 r hr η
      change (redMap q r i).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = _
      rw [GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ η hη, GlobalTheory.T.tateTwistReductionResolutionMap_generator q r hr i U η ξ hξ,
        GlobalTheory.T.tateTwistReductionResolutionMap_generator Q r hrQ i U ζ ξ (by rw [hξ, hη, ← pow_mul, div_mul_div hqQ hr])]
    exact (semiComp_op _ _ E n a).symm.trans (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q r hrQ i _ _ hgen E n a)

end GlobalTheory.EtC.RedCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickening
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q) (q : Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → HasVal p (fun j => E (u j)) f q → HasVal p z (subst (up Q u) f) q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u f q hu hf hq
  intro m
  obtain ⟨M0, hM0⟩ := _root_.GlobalTheory.tail_subst_small p B O Q θ hF σ z hz τ u f hu hf m
  obtain ⟨M1, hM1⟩ := hq m
  obtain ⟨g, hg⟩ : ∃ g : MvPolynomial τ Q, g = trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max M0 M1) f := ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ := _root_.GlobalTheory.QLog.hasVal_subst_poly p B O Q θ hF σ z hz E hE τ u hu g m
  refine ⟨N2, fun N' hN' => ?_⟩
  obtain ⟨b1, hb1⟩ := hM1 (max M0 M1) (le_max_right _ _)
  obtain ⟨b2, hb2⟩ := hN2 N' hN'
  obtain ⟨b3, hb3⟩ := hM0 (max M0 M1) (le_max_left _ _) (Finsupp.equivFunOnFinite.symm fun _ => N')
  rw [← hg] at hb1 hb3
  have hs : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  have hsplit : subst (up Q u) f = subst (up Q u) (g : MvPowerSeries τ Q) + subst (up Q u) (f - (g : MvPowerSeries τ Q)) := by
    rw [← subst_add hs]; congr 1; ring
  refine ⟨b1 + b2 - b3, ?_⟩
  rw [hsplit, map_add (f := _), map_add (f := _)]
  simp only [map_mul, map_sub, map_add (f := _), map_pow, map_natCast] at hb1 hb2 hb3 ⊢
  linear_combination hb1 + hb2 - hb3

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIdempotentSplitField
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem idempotent_split (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k)
    (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧
      ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  obtain ⟨h₀, hrank⟩ := @kerIdeal_finrank_eq_pow_of_idempotent p _ k _ G u v huv h1 h2
  obtain ⟨K, i, hi⟩ := @KerGrp.exists_kernel p _ k _ G u h₀ hrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p k K G i (fun n => (hi n).1)
  have hvu : v + u = 𝟙 G := by rw [add_comm]; exact huv
  have hker : ∀ n, RingHom.ker (i.app n) = RingHom.ker (v.app n) := fun n => by
    rw [(hi n).2, ker_app_eq_kerIdeal_of_idempotents p k G v u hvu h2 h1 n]
  obtain ⟨q, hq⟩ := hfac G v (fun n => (hker n).le)
  have hiu : i ≫ u = 0 := by
    refine Hom.ext (funext fun n => BialgHom.ext fun b => ?_)
    have h := (kerIdeal_le_ker_iff (u.app n) (i.app n : G.A n →ₐ[k] K.A n)).1 (hi n).2.ge b
    change i.app n (u.app n b) = (1 : WithConv (G.A n →ₐc[k] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiv : i ≫ v = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiu, zero_add, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq, hi⟩
  apply hcan K
  rw [Category.assoc, hq, hiv, Category.id_comp]

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagImStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), (dY X z τ a a).im = 0 := by
  first | exact @GlobalTheory.SUChartSection.diagreal | exact GlobalTheory.SUChartSection.diagreal | (intros; apply GlobalTheory.SUChartSection.diagreal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkewStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a b : Fin r), dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  first | exact @GlobalTheory.SUChartSection.dY_skew | exact GlobalTheory.SUChartSection.dY_skew | (intros; apply GlobalTheory.SUChartSection.dY_skew <;> assumption)
end

