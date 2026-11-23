module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

theorem range_sub_iff {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (W : Set X) (p₀ : Sp k) :
    Set.range x.base ⊆ W ↔ x.base p₀ ∈ W := by
  refine ⟨fun H => H ⟨p₀, rfl⟩, ?_⟩
  rintro H _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p p₀]


open GlobalTheory.SiegelPull in
theorem exists_open_sympLev : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  intro h M S' _ t G _ _ P lev hab hP hr₁ hr₂ hsy hM hodd hadd htor
  let Good : S'.Opens → Prop := fun W => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S')
    (β : cycAway M →+* k) (z : kˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      SympAt P h M lev k x z
  have hsup : ∀ (k : Type) [Field k] (x : Sp k ⟶ S'), Set.range x.base ⊆ (sSup {W | Good W} : S'.Opens) →
      ∃ W, Good W ∧ Set.range x.base ⊆ W := by
    intro k _ x hx
    let p₀ : Sp k := (⊥ : PrimeSpectrum k)
    rw [range_sub_iff x _ p₀] at hx
    obtain ⟨W, hW, hpW⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨W, hW, (range_sub_iff x _ p₀).2 hpW⟩
  refine ⟨sSup {W | Good W}, fun V hV => ?_, ?_⟩
  · have pb := Pdiv.PullbackComparison.isGrpPullback V.ι G
    refine (isSympLev_iff _ _ _ _ _ _).2 ⟨fun a b => push_injective pb _ ?_, fun a => push_injective pb _ ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · rw [map_mul, push_secPull', push_secPull', push_secPull', hadd, MonObj.comp_mul]
    · rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, htor, MonObj.comp_one]
    · rw [sympAt_pullback_iff V.ι hP (pull_isLB hP _) pb (Pdiv.PullbackComparison.isSquare V.ι G)
        (Pdiv.PullbackComparison.gen_refl _ (pull_isLB hP _)) (fun a => secPull_left pb _)]
      obtain ⟨W, hW, hxW⟩ := hsup k (x ≫ V.ι) (by
        rintro _ ⟨p, rfl⟩
        exact hV (by first | exact (x.base p).2 | simp | (rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩)))
      exact hW k (x ≫ V.ι) β z hxW (by rw [Category.assoc]; exact hx) hz
  · intro T g c' φ φ₂ pb sq iso hl
    rintro _ ⟨τ, rfl⟩
    obtain ⟨K, _, _, x₀, ⟨q, hq⟩⟩ := GlobalTheory.SiegelTypings.exists_geomPt τ
    obtain ⟨β, hβ⟩ := (⟨(Spec.preimage (x₀ ≫ g ≫ t)).hom, by simp [spMap]⟩ : ∃ β : cycAway M →+* K, spMap β = x₀ ≫ g ≫ t)
    let z : Kˣ := ((GlobalTheory.LowChart.isUnit_zetaAway M hM).map β).unit
    have hc : SympAt c'.P h M c'.lev K x₀ z := c'.geom K x₀ β z hβ.symm rfl
    obtain ⟨hS₁, hS₂, hS₃⟩ := (sympAt_pullback_iff g hP c'.isLB pb sq iso hl K x₀ z).1 hc
    have e₁ := GlobalTheory.T.level_sections_exact_kernel_locus_open S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₂ := GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₃ := GlobalTheory.T.symmetric_bundle_level_odd S' M t G P h lev hab hP hr₁ hr₂ hsy hM hodd hadd htor K (x₀ ≫ g) β z (by rw [Category.assoc, hβ]) rfl
    obtain ⟨W₁, hW₁, H₁⟩ := e₁ hS₁
    obtain ⟨W₂, hW₂, H₂⟩ := e₂ hS₂
    obtain ⟨W₃, hW₃, H₃⟩ := e₃ hS₃
    have hgood : Good (W₁ ⊓ W₂ ⊓ W₃) := fun k _ _ x β' z' hx hxt hz' =>
      ⟨H₁ k x (hx.trans (le_trans inf_le_left inf_le_left)), H₂ k x (hx.trans (le_trans inf_le_left inf_le_right)),
        H₃ k x β' z' (hx.trans inf_le_right) hxt hz'⟩
    have hmem : g.base τ ∈ (W₁ ⊓ W₂ ⊓ W₃ : S'.Opens) := by
      have e : (x₀ ≫ g).base q = g.base τ := by first | simp [← hq] | (rw [Scheme.Hom.comp_apply, hq]) | (rw [Scheme.comp_base_apply, hq])
      rw [← e]
      exact ⟨⟨hW₁ ⟨q, rfl⟩, hW₂ ⟨q, rfl⟩⟩, hW₃ ⟨q, rfl⟩⟩
    exact (le_sSup (show W₁ ⊓ W₂ ⊓ W₃ ∈ {W | Good W} from hgood)) hmem

end GlobalTheory.SympLevLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Principal

theorem of_isEmpty {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Type} [CommRing S]
    [IsEmpty (Sp S)] (t : SAB H (Sp S)) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  refine ⟨inferInstance, ?_, fun T _ s x _ => ?_⟩
  · have := t.semi.quasiCompact
    have := t.semi.separated
    exact GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance
      fun q => isEmptyElim q
  · have : IsEmpty (Over.mk s).left := ⟨fun p => isEmptyElim (s p)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := (Over.mk s).left)).hom_ext _ _)

theorem isProper_relAmple_kTriv_of_psiUnitOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (f : R), (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∀ tO : SAB H (Sp (Localization.Away f)), SABMap tO t (spMap (algebraMap R (Localization.Away f))) → IsProper tO.G.hom ∧ Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
  intro E _ _ _ H R _ _ _ hR t P f hψ tf mf
  let Rf := Localization.Away f
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  by_cases hf : f = 0
  · have : IsEmpty (Sp Rf) := ⟨fun z => by
      have hz : f ∉ (spMap (algebraMap R Rf) z).asIdeal := hrange.le ⟨z, rfl⟩
      exact hz ((congrArg (· ∈ (spMap (algebraMap R Rf) z).asIdeal) hf).mpr (Ideal.zero_mem _))⟩
    exact of_isEmpty tf
  obtain ⟨hab, -⟩ := GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn R hR P.D P.A t.G t.semi P.U
    (PrimeSpectrum.basicOpen f) hψ
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 (hab (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  exact ⟨hpf, GlobalTheory.AbLocusPol.relAmple_kTriv_of_generic tf hpf hg⟩

end GlobalTheory.UCanon.Principal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmBasisReductionThickening
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReduceBasis

section Ring

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_neg {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (-f) := by
  simpa using KLift.in_sub in_zero hf

theorem in_smul (r : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal B) (algebraMap B Q r • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨r * b, trivial, by rw [coeff_smul, hb, map_mul]⟩

theorem in_sum {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i, In (⊤ : Ideal B) (f i)) : In (⊤ : Ideal B) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q))
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact KLift.in_add (hf a) ih

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem comb_sub (x y : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb x e - comb y e = comb (x - y) e := by
  simp only [comb, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub, sub_smul]

theorem comb_single [DecidableEq ι] (l : ι) (e : ι → MvPowerSeries σ Q) :
    comb (Pi.single l (1 : B)) e = e l := by
  rw [comb, Finset.sum_eq_single l (fun j _ hj => by simp [Pi.single_apply, hj])
    (fun h => absurd (Finset.mem_univ l) h)]
  simp

theorem comb_comb (M : κ → B) (N : κ → ι → B) (e : ι → MvPowerSeries σ Q) :
    ∑ m, algebraMap B Q (M m) • comb (N m) e = comb (fun l => ∑ m, M m * N m l) e := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem mul_eq_single [DecidableEq ι] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {e : ι → MvPowerSeries (Fin d) Q} {f : κ → MvPowerSeries (Fin d) Q} (he : IsBasis μ e)
    (M : ι → κ → B) (N : κ → ι → B) (hM : ∀ l, In (⊤ : Ideal B) (e l - comb (M l) f))
    (hN : ∀ m, In (⊤ : Ideal B) (f m - comb (N m) e)) (l : ι) :
    (fun l' => ∑ m, M l m * N m l') = Pi.single l 1 := by
  refine (he.2 (e l) (he.1 l)).unique ?_ ?_
  · have hs : e l - comb (fun l' => ∑ m, M l m * N m l') e =
        (e l - comb (M l) f) + ∑ m, algebraMap B Q (M l m) • (f m - comb (N m) e) := by
      simp only [smul_sub, Finset.sum_sub_distrib, comb_comb]
      simp only [comb]; abel
    rw [hs]
    exact KLift.in_add (hM l) (in_sum _ _ fun m => in_smul _ (hN m))
  · rw [comb_single, sub_self]; exact in_zero

end Ring

section Map

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {σ : Type} {θ : B →+* O} {Θ : Q →+* C}
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))

include hΘ in
theorem in_map {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem map_smul_series (c : Q) (f : MvPowerSeries σ Q) : map Θ (c • f) = Θ c • map Θ f := by
  ext α
  simp [coeff_map, coeff_smul]

include hΘ in
theorem map_comb {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_smul_series, hΘ]

end Map

end GlobalTheory.ReduceBasis

namespace GlobalTheory.ReduceBasis

theorem isBasis_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → IsBasis c.μ (fun l => map Θ (e l)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e he Θ hΘ
  classical
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := KLift.const_map _ μ' hL.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := KLift.const_map _ _ c.isLaw.const
  have hΘμ : (fun i => map Θ (up F.Q μ' i)) = up C c.μ := by
    have hc : Θ.comp (algebraMap F.B F.Q) = (algebraMap O C).comp F.θ := RingHom.ext hΘ
    funext i
    unfold up
    rw [← hμ i, ← RingHom.comp_apply (map Θ), ← map_comp,
      ← RingHom.comp_apply (map (algebraMap O C)), ← map_comp, hc]
  have hQL : ∀ f, QL μ' ⊤ f → QL c.μ ⊤ (map Θ f) := by
    rintro f ⟨h0, h1, h2⟩
    refine ⟨?_, fun i => ?_, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
        map_zero]
    · obtain ⟨b, -, hb⟩ := h1 i
      refine ⟨F.θ b, trivial, ?_⟩
      simp only [lin, coeff_map] at hb ⊢
      rw [hb, hΘ]
    · rw [← hΘμ, ← KLift.map_formalGroupLawCoboundaryOne_eq Θ _ hμQ]
      exact in_map hΘ h2

  have hlift : ∀ g, QL c.μ ⊤ g → ∃ f, QL μ' ⊤ f ∧ map Θ f = g := by
    intro g hg
    choose o _ ho using hg.2.1
    choose w hw using fun i => F.frame.surj (o i)
    obtain ⟨f, hf, hfg, -⟩ := KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ g w
      (by rw [hcμ]; exact hg) (fun i => by rw [ho, hw])
    exact ⟨f, hf, hfg⟩
  have key : ∀ x : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (comb x fun l => map Θ (e l)) → x = 0 := by
    intro x hx
    obtain ⟨k0, e0, -, he0, -⟩ := _root_.GlobalTheory.QLogBasis.adapted_basis p C v O hv G d c C hC
    choose f hf hfe using fun m => hlift (e0 m) (he0.1 m)
    have hfB : IsBasis μ' f := GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ _ f hf
      (by rw [hcμ]; simpa only [hfe] using he0) (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    choose M hM _ using fun l => hfB.2 (e l) (he.1 l)
    choose N hN _ using fun m => he.2 (f m) (hf m)
    have hMN := mul_eq_single he M N hM hN
    set y : Fin d ⊕ Fin k0 → O := fun m => ∑ l, x l * F.θ (M l m) with hydef
    have hy : In (⊤ : Ideal O) (comb y e0) := by
      have hs : comb y e0 = comb x (fun l => map Θ (e l)) -
          ∑ l, algebraMap O C (x l) • map Θ (e l - comb (M l) f) := by
        simp only [map_sub, map_comb hΘ, hfe, smul_sub, Finset.sum_sub_distrib, comb_comb, hydef]
        simp only [comb]
        abel
      rw [hs]
      exact KLift.in_sub hx (in_sum _ _ fun l => in_smul _ (in_map hΘ (hM l)))
    have h0 : QL c.μ ⊤ (0 : MvPowerSeries (Fin d) C) := by
      refine ⟨by simp, fun i => ⟨0, trivial, by simp [lin]⟩, ?_⟩
      have : cob1 (up C c.μ) (0 : MvPowerSeries (Fin d) C) = 0 := by
        simpa using formalCoboundary_smul hμC (0 : C) (0 : MvPowerSeries (Fin d) C)
      rw [this]
      exact in_zero
    have hy0 : y = 0 := by
      refine (he0.2 0 h0).unique ?_ ?_
      · simpa using in_neg hy
      · have : comb (0 : Fin d ⊕ Fin k0 → O) e0 = 0 := by simp [comb]
        rw [this, sub_zero]
        exact in_zero
    funext l'
    have e1 : ∀ l, F.θ (∑ m, M l m * N m l') = if l' = l then 1 else 0 := fun l => by
      have h1 := congrFun (hMN l) l'
      rw [h1, Pi.single_apply]
      split_ifs <;> simp
    have s1 : x l' = ∑ l, x l * F.θ (∑ m, M l m * N m l') := by
      simp only [e1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have s2 : ∑ l, x l * F.θ (∑ m, M l m * N m l') = ∑ m, y m * F.θ (N m l') := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hydef, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    rw [s1, s2, hy0]
    simp
  refine ⟨fun l => hQL _ (he.1 l), fun g hg => ?_⟩
  obtain ⟨f, hf, hfg⟩ := hlift g hg
  obtain ⟨b, hb, -⟩ := he.2 f hf
  have hx0 : In (⊤ : Ideal O) (g - comb (fun l => F.θ (b l)) fun l => map Θ (e l)) := by
    have := in_map hΘ hb
    rwa [map_sub, hfg, map_comb hΘ] at this
  refine ⟨fun l => F.θ (b l), hx0, fun y hy => ?_⟩
  have h := key ((fun l => F.θ (b l)) - y) (by
    rw [← comb_sub]
    convert KLift.in_sub hy hx0 using 1
    abel)
  exact (sub_eq_zero.1 h).symm

end GlobalTheory.ReduceBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USep

open GlobalTheory.TorsFrame

theorem isTorsFrame_sq : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S)
    (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
    IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  intro S P rig n T x τ ⟨hx, hτ, α, hα, hN, hC⟩
  have hL := P.isLB
  have eN : (mulA P.A n).left ≫ (mulA P.A n).left = (mulA P.A (n ^ 2)).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← sq]
  have ex : x.left ≫ (mulA P.A n).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx, one_left]
  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, eN]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (mulA P.A n).left) (GeneratorPullback.powGen P.L _ _ α (n ^ 2)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.powGen_isGen _ _ _ _ hα _))
  have vα₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
      val α' r z J = val α (r ≫ (mulA P.A n).left) z J * val α r z J ^ (n ^ 2) := fun Z r z J hJ => by
    rw [vα' _ _ z J hJ, val_mul hJ, val_pull hJ, val_powGen]
  refine ⟨by rw [sq, pow_mul, hx, one_pow], hτ, α', hα', corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · have h0 := val_corr hJ hN (𝟙 (𝟙_ (Over S)).left)
    rw [val_pull hJ, val_mul hJ, val_inv] at h0 ⊢
    rw [vα₂ _ _ z J hJ, Category.assoc, eSec_mulA, h0]
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) (𝟙 (𝟙_ (Over S)).left) z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig (𝟙 (𝟙_ (Over S)).left) z J ^ k := fun k => map_zpow _ _ _
    rw [hp, hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module
  · have h1 := val_corr hJ hC (𝟙 T.left)
    have h2 := val_corr hJ hN T.hom
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) T.hom z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J ^ k := fun k => map_zpow _ _ _
    have hf : ∀ k : ℤ, val (powFrame P.A P.L x τ k) (𝟙 T.left) z J = val τ (𝟙 T.left) z J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, val_inv, hp] at h2
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ] at h1
    simp only [Category.id_comp] at h1
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ]
    simp only [Category.id_comp]
    rw [vα₂ _ _ z J hJ, ex, h2]
    have ha : val α x.left z J = val τ (𝟙 T.left) z J ^ ((n : ℤ) ^ 2) *
        (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J)⁻¹ := by
      rw [h1, mul_inv_cancel_right]
    rw [ha]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitCoefficientOfThetaSquareIntegralTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic


set_option maxHeartbeats 400000 in
theorem GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)),
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) →
    ∃ c₁ : C, ∀ (G : V₁) (U : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Sp V₁) (z : Z) (_ : (Z ⟶ D.P.A.left) → D.P.L.ι),
        (Z.presheaf.stalk z)ˣ),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c₁).left) z J ^ 2 *
            (U Z r z J).val) → IsUnit G := by
  intro N₁ hN V₁ _ _ _ hV hunit D θ hθ C b hcov
  let K := AlgebraicClosure (ResidueField V₁)
  let ev : V₁ →+* K := (algebraMap (ResidueField V₁) K).comp (residue V₁)
  have hθ' : ∃ j, (ThetaOne.pullTo D ev θ).f j ≠ 0 :=
    ThetaOne.exists_ne_zero D ev _ (hθ K ev _ (ThetaOne.isPullSecLC_pullTo D ev θ))
  have hNK : (N₁ : K) ≠ 0 := by
    have := (hunit N₁ (by omega)).map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨p, hp, hne⟩ := GlobalTheory.Poinc.Sep.Coef.exists_torsion_ne D ev θ hθ' N₁ hN hNK
  obtain ⟨c₁, hc⟩ := hcov K (spMap ev) p hp
  refine ⟨c₁, fun G U hG => ?_⟩
  by_contra hGu
  have hG0 : ev G = 0 := by
    show algebraMap (ResidueField V₁) K (residue V₁ G) = 0
    rw [(residue_eq_zero_iff G).2 ((mem_maximalIdeal G).2 hGu), map_zero]
  let z : Sp K := IsLocalRing.closedPoint K
  have hch : ∀ ψ : Sp K ⟶ D.P.A.left, ∃ i, ψ z ∈ D.P.L.U i := fun ψ =>
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ z)
  choose J hJ using hch
  have hgood : Good D.P.L z J := hJ
  have e := hG (Sp K) (spMap ev) z J hgood
  have e2 : gs (spMap ev) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) = toStk z (ev G) := by
    have := GlobalTheory.Poinc.Sep.Coef.gs_ev ev ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) z
    simpa using this
  have hpl : p.left = spMap ev ≫ (b c₁).left := by rw [hc]; rfl
  have h1 := hne z J hgood
  rw [hpl] at h1
  obtain ⟨y, hy⟩ := GlobalTheory.Poinc.Sep.Coef.toStk_surj z (sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ (b c₁).left) z J)
  rw [e2, hG0, map_zero, ← hy, ← map_pow] at e
  have h3 : toStk z (y ^ 2) = 0 := (Units.mul_left_eq_zero _).1 e.symm
  have h4 : y ^ 2 = 0 := (toStk z).injective (h3.trans (map_zero _).symm)
  exact h1 (by rw [← hy, pow_eq_zero_iff two_ne_zero |>.1 h4, map_zero])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleIsomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_bundle_isomorphism : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  first | (exact @GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (exact GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (intros; apply GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion  <;> assumption)
end

