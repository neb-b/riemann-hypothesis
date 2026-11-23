module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1BijectiveOfExhaustingFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRestrictionFourTermComplexOfExhaustion
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzEtDualOfIso
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem isConn_of_chart {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k) {d : ℕ}
    (c : Katz.Chart G d) : G.IsConn := by
  intro n a ha
  obtain ⟨f, rfl⟩ := c.presents.1 n a
  have h0 : Coalgebra.counit (R := k) (Katz.evA k (c.x n) (c.nil n) f) = 0 := by
    have := RingHom.mem_ker.1 ha
    simpa using this
  have hf : MvPowerSeries.constantCoeff f = 0 := by
    rw [← (Katz.counit_dUnit_evA k d (G.A n) (c.x n) (c.nil n) (c.aug n) f).1]; exact h0
  exact mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero k (Fin d) (G.A n)
    (Katz.evA k (c.x n) (c.nil n)) (fun i => by rw [Katz.evA_X]; exact c.nil n i) f hf

end GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem katz_etDual_of_iso : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))
    (C : Base p (fun _ _ G => G.IsEt)) (D : Base p (fun _ _ _ => True)), B.Katz → C.EtDual B →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn),
      D.M G trivial ≃ₗ[WittVector p k] B.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsConn) (h : G.IsConn) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = B.smap h' h s (e G h m)) →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt),
      D.M G trivial ≃ₗ[WittVector p k] C.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = C.smap h' h s (e G h m)) →
    D.Katz ∧ D.EtDual D := by
  intro p _ B C D hB hC ⟨eB, neB⟩ ⟨eC, neC⟩
  obtain ⟨κ, hκ⟩ := hB
  obtain ⟨δ, hδ⟩ := hC

  have FB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn)
      (t : True) (m : D.M G trivial), eB G h (D.F G t m) = B.F G h (eB G h m) := fun G h _ m =>
    neB _ _ _ G G h h _ m
  have FC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt)
      (t : True) (m : D.M G trivial), eC G h (D.F G t m) = C.F G h (eC G h m) := fun G h _ m =>
    neC _ _ _ G G h h _ m
  have MB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsConn)
      (h' : H.IsConn) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eB G h (D.map t t' f m) = B.map h h' f (eB H h' m) := fun G H h h' f _ _ m =>
    neB _ _ _ G H h h' _ m
  have MC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsEt)
      (h' : H.IsEt) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eC G h (D.map t t' f m) = C.map h h' f (eC H h' m) := fun G H h h' f _ _ m =>
    neC _ _ _ G H h h' _ m
  refine ⟨⟨fun {_} _ _ _ G _ {_} c {_} hμ hc => (eB G (isConn_of_chart G c)).trans (κ G _ c hμ hc), ?_⟩,
    ⟨fun G _ _ hG => (eC G hG).trans ((δ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG).trans
      (eB G.dual (PDivGroup.dual_isConn_of_isEt p _ G hG)).dualMap), ?_⟩⟩
  · intro k _ _ _ G _ d c μ hμ hc
    obtain ⟨h1, h2⟩ := hκ G (isConn_of_chart G c) c hμ hc
    refine ⟨?_, ?_⟩
    · convert h1 using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, FB, LinearEquiv.apply_symm_apply]
    · intro H _ d' c' ν hν hc' f φ hφ hm
      convert h2 H (isConn_of_chart H c') c' hν hc' f φ hφ hm using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
        MB G H (isConn_of_chart G c) (isConn_of_chart H c'), LinearEquiv.apply_symm_apply]
  · intro k _ _ _ G _ _ hG
    obtain ⟨h1, h2⟩ := hδ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG
    refine ⟨fun x y => ?_, fun H _ _ hH f x y => ?_⟩
    · simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, FB, FC]
      exact h1 _ _
    · obtain ⟨-, h3⟩ := hδ H hH (PDivGroup.dual_isConn_of_isEt p _ H hH) hH
      simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
      rw [MC G H hG hH f, MB H.dual G.dual (PDivGroup.dual_isConn_of_isEt p _ H hH)
        (PDivGroup.dual_isConn_of_isEt p _ G hG) (G.dualHom H f)]
      exact h2 H hH _ hH f _ _

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionLocallyCutOutByIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : OActN D.O A) (z : S),
  ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'), spMap f ≫ hU.fromSpec ≫ s = spMap β →
      (LieHer b act β (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.lieHer_ideal) | (exact GlobalTheory.UPel.HT.LieLin.lieHer_ideal) | (intros; apply GlobalTheory.UPel.HT.LieLin.lieHer_ideal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjective
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_ge_finrank_of_semilinear_surj (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U]
    [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U) :
    Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) →
    ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) →
      (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧
      ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  intro hθ hsemi L
  let σ : WittVector p k →+* k := (WittVector.constantCoeff).comp e.symm.toRingHom
  have hσ : Function.Surjective σ := by
    intro x
    obtain ⟨a, ha⟩ : ∃ a : WittVector p k, WittVector.constantCoeff a = x :=
      ⟨WittVector.teichmuller p x, by simp⟩
    exact ⟨e a, by simp [σ, ha]⟩
  letI : Algebra (WittVector p k) k := σ.toAlgebra
  letI : Module (WittVector p k) U := Module.compHom U σ
  haveI : IsScalarTower (WittVector p k) k U :=
    ⟨fun a b u => by
      show (σ a * b) • u = σ a • (b • u)
      exact mul_smul _ _ _⟩
  have hlenU : Module.length (WittVector p k) U = Module.finrank k U := by
    rw [Module.length_eq_of_surjective (R := k) (S := WittVector p k) (M := U) hσ,
      Module.length_eq_finrank]
  let θl : N →ₗ[WittVector p k] U :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun a n => by
        have h := hsemi (e.symm a) n
        rw [RingEquiv.apply_symm_apply] at h
        exact h }
  have hθl : Function.Surjective θl := hθ
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · have hle : L ≤ LinearMap.ker θl := fun n hn => hL n hn
    rw [← hlenU]
    exact Module.length_le_of_surjective (L.liftQ θl hle) (by
      intro u
      obtain ⟨n, rfl⟩ := hθl u
      exact ⟨Submodule.Quotient.mk n, rfl⟩)
  · have hK : L = LinearMap.ker θl := by
      ext n
      exact hL n
    rw [← hlenU, hK]
    exact (θl.quotKerEquivOfSurjective hθl).length_eq

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPart
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CentLev

theorem loc_cpt_part {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : UL n w) (hs : y.1.val.charpoly.Separable) :
    ∃ C : Set (UL n w), IsCompact C ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ C := by
  obtain ⟨Ω, hΩ, hmem⟩ := GlobalTheory.CentCpt.main E hU n w y hs
  haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a * y = y * a := ha
    have hb' : b * y = y * b := hb
    have hav : (a : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (a : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) ha'; simpa using this
    have hbv : (b : GLw n w).val * (y : GLw n w).val = (y : GLw n w).val * (b : GLw n w).val := by
      have := congrArg (fun z : UL n w => (z : GLw n w).val) hb'; simpa using this
    have := GlobalTheory.commute_of_commute_separable_charpoly _ n _ _ _ hs hav hbv
    apply Subtype.ext; apply Units.ext; simpa using this
  refine ⟨Ω, hΩ, fun z hz => ?_⟩
  obtain ⟨hzT, hzc⟩ := GlobalTheory.LocFinU.cptPart_subset_of_comm _ hc hz
  exact hmem z hzT hzc

theorem stab_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU (E := E) (n := n), twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ)) ∧ (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ))) ≠ 0 := by
  intro E _ _ _ hU n hn S hS K' hK' γ hγ x
  set δ : finU (E := E) (n := n) := finPt γ with hδ
  set T := twCent (MonoidHom.id (finU (E := E) (n := n))) δ with hT
  let ρ : ∀ w : Pl E, finU (E := E) (n := n) →* UL n w := fun w =>
    { toFun := fun z => ⟨cLoc w (z : UA E n), GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hρv : ∀ w z, ((ρ w z : UL n w) : GLw n w) = cLoc w (z : UA E n) := fun _ _ => rfl
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    continuous_induced_rng.2 ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)
  have hδw : ∀ w, ((ρ w δ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
    intro w
    rw [hρv, hδ, FinPtLoc.finPt_eq]
    apply Units.ext
    refine Matrix.ext fun i j => ?_
    change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
    rw [FinPtLoc.snd_entry]
    rfl
  have hsep : ∀ w, ((ρ w δ : UL n w) : GLw n w).val.charpoly.Separable := by
    intro w
    rw [hδw]
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = γ.1.val.map (algebraMap E _) := rfl
    rw [e, Matrix.charpoly_map]
    exact hγ.map
  have hsetK : ∀ K'' : ∀ w : Pl E, Subgroup (UL n w), (globLev S K'' : Set (finU (E := E) (n := n))) =
      {z : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ (K'' w : Set (UL n w))} := by
    intro K''
    ext z
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    refine forall₂_congr fun w _ => ?_
    rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
    constructor
    · rintro ⟨a, ha, e⟩
      have : a = ⟨_, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (z : UA E n)⟩ := Subtype.ext e
      rwa [← this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hKc : IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [hsetK]
    exact GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => (KL n w : Set (UL n w)))
      (fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2) (Filter.Eventually.of_forall fun _ => rfl)
  have hcf : ⇑((MulAut.conj x).toMonoidHom) = fun g : finU (E := E) (n := n) => x * g * x⁻¹ := by
    ext g; simp
  have hconj : ∀ H : Subgroup (finU (E := E) (n := n)), (H.map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) =
      (fun g => x⁻¹ * g * x) ⁻¹' (H : Set (finU (E := E) (n := n))) := by
    intro H; ext g
    rw [Subgroup.coe_map, hcf]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  refine ⟨?_, ?_⟩
  · rintro t ⟨htT, htK⟩
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hKx : IsCompact ((globLev S (KL n)).map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) := by
      rw [Subgroup.coe_map, hcf]
      exact hKc.image (by fun_prop)
    set_option synthInstance.maxHeartbeats 200000 in
      exact hKx.closure_of_subset fun s hs => Subgroup.zpowers_le.2 htK hs
  · have hUo : IsOpen ((globLev S K').map (MulAut.conj x).toMonoidHom : Set (finU (E := E) (n := n))) := by
      rw [hconj]
      exact (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK').preimage (by fun_prop)
    choose C0 hC0c hC0 using fun w => loc_cpt_part hU n w (ρ w δ) (hsep w)
    have hcof := _root_.GlobalTheory.BCT.GoodCpt.main E hU n γ hγ
    let C : ∀ w : Pl E, Set (UL n w) := fun w =>
      if cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w then (KL n w : Set (UL n w)) else C0 w
    have hCc : ∀ w, IsCompact (C w) := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
      · simp only [C, if_neg h]; exact hC0c w
    have hCK : ∀ᶠ w in cofinite, C w = KL n w := by
      filter_upwards [hcof] with w hw
      have e : ρ w δ = locPt w γ := by
        rw [← GlobalTheory.BCT.locPt_finPt E hU n γ w, FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
        rfl
      have hw' : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w := by rw [e]; exact hw
      simp only [C, if_pos hw']
    have hsub : ∀ w, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) : Set (UL n w)) ⊆ C w := by
      intro w
      by_cases h : cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ)) ≤ KL n w
      · simp only [C, if_pos h]; exact h
      · simp only [C, if_neg h]; exact hC0 w
    have hD := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS C hCc hCK
    have hle : cptPart T ≤ ⨅ w : Pl E, (cptPart (twCent (MonoidHom.id (UL n w)) (ρ w δ))).comap (ρ w) := by
      rw [cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      rw [SetLike.mem_coe, Subgroup.mem_iInf]
      intro w
      rw [Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · have ht' : t * δ = δ * t := htT
        show ρ w t * ρ w δ = ρ w δ * (MonoidHom.id _) (ρ w t)
        rw [MonoidHom.id_apply, ← map_mul, ht', map_mul]
      · have himc : IsCompact (ρ w '' closure (Subgroup.zpowers t : Set (finU (E := E) (n := n)))) := htc.image (hρc w)
        refine himc.closure_of_subset ?_
        rintro _ ⟨k, rfl⟩
        exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have hTD : (cptPart T : Set (finU (E := E) (n := n))) ⊆
        {z : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (z : UA E n)) ∈ C w} := by
      intro z hz w _
      have hzw := Subgroup.mem_iInf.1 (hle hz) w
      rw [Subgroup.mem_comap] at hzw
      rw [FinPtLoc.toSub_of_mem _ _ (GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w _)]
      exact hsub w hzw
    have hUo' : IsOpen ((((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) : Subgroup _) :
        Set (cptPart T)) := by
      rw [Subgroup.coe_subgroupOf]
      exact hUo.preimage continuous_subtype_val
    have hfi := GlobalTheory.LocVec.finiteIndex_of_isOpen (cptPart T) hD hTD _ hUo'
    have hTc : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
    have heq : (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) =
        ((globLev S K').map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart T) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hTc z.2, h⟩⟩
    rw [Subgroup.relIndex, heq]
    exact hfi.index_ne_zero

end GlobalTheory.BCT.CentLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegrees
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem resMap_bij12_of_fnMap {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (K : Cx C) (G : C' ⥤ C)
    (h : K.fnMap.PullbackBijectiveDegreesOneTwo) (h' : (K.res G).fnMap.PullbackBijectiveDegreesOneTwo) (h₀ : ((Cx.single K.M0).resMap G).PullbackBijectiveDegreesOneTwo) :
    (K.resMap G).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : (K.res G).fnMap.h1 ∘ (K.resMap G).h1 = ((Cx.single K.M0).resMap G).h1 ∘ K.fnMap.h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.1 _).1 (e ▸ h₀.1.comp h.1)
  · have e : (K.res G).fnMap.h2 ∘ (K.resMap G).h2 = ((Cx.single K.M0).resMap G).h2 ∘ K.fnMap.h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.2 _).1 (e ▸ h₀.2.comp h.2)

theorem resMap_comp_bij12 {C C' : Type 1} {C'' : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    (K : Cx C) (G : C' ⥤ C) (H : C'' ⥤ C') (h : (K.resMap G).PullbackBijectiveDegreesOneTwo) (h' : ((K.res G).resMap H).PullbackBijectiveDegreesOneTwo) :
    (K.resMap (H ⋙ G)).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : ⇑(K.resMap (H ⋙ G)).h1 = ((K.res G).resMap H).h1 ∘ (K.resMap G).h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.1.comp h.1
  · have e : ⇑(K.resMap (H ⋙ G)).h2 = ((K.res G).resMap H).h2 ∘ (K.resMap G).h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.2.comp h.2

theorem Lift.resMap_toE_pullbackBijectiveDegreesOneTwo (D : Data) (Λ : Lift D) :
    (((KK D.κ D.t).res (pE D.κ D.t D.i)).resMap Λ.toE).PullbackBijectiveDegreesOneTwo := by
  obtain ⟨N₀, hN₀⟩ := (_root_.GlobalTheory.PDForm.Lift.hom_spec D Λ).2.2.2
  have mono : ∀ m n T, m ≤ n → LevE D.κ D.t D.i m T → LevE D.κ D.t D.i n T := fun m n T hmn hT ↦
    le_bot_iff.1 (((fil_properties _ _ T.obj.T.δ).2.2.1 m n hmn).trans (le_of_eq hT))
  have exh : ∀ T, ∃ n, LevE D.κ D.t D.i n T := fun T ↦ (isDPNilpotent_iff_exists_isLevel T.obj.T.δ).1 T.obj.T.nil
  have lev : ∀ N, N₀ + 1 ≤ N → ∃ h : ∀ U, LevE D.κ D.t D.i N (Λ.toE.obj U),
      ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i N).ι).resMap
        ((LevE D.κ D.t D.i N).lift Λ.toE h)).Bij := by
    intro N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact ⟨fun U ↦ hN₀ _ (by omega) U, _root_.GlobalTheory.PDForm.levLift_resMap_bij D Λ n _⟩
  exact ⟨_root_.GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion _ _ _ _ Λ.toE (N₀ + 1) mono exh lev, _root_.GlobalTheory.CxTowerTwo.tower_two _ _ _ _ Λ.toE (N₀ + 1) mono exh lev⟩

theorem Lift.resMap_lift_pullbackBijectiveDegreesOneTwo : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  intro D Λ
  have hp := GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ _ D.t _ D.i
  have hg := _root_.GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs D.R D.I D.κ _ D.t _ D.i D.smooth_mono_inf.2.2
  exact resMap_comp_bij12 (KK D.κ D.t) (pE D.κ D.t D.i) Λ.toE
    (resMap_bij12_of_fnMap _ _ hp.1 hp.2 hg) (Lift.resMap_toE_pullbackBijectiveDegreesOneTwo D Λ)

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem int_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ), Intg (Function.update L i A) f → Intg (Function.update L i B) f → Intg (Function.update L i (A.tens B)) f ∧ Mix.int (Function.update L i (A.tens B)) f = Mix.int (Function.update L i A) f + Mix.int (Function.update L i B) f := by
  intro k _ X p σ hp D L i A B f hA hB
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have h := _root_.GlobalTheory.Mix.int_add_of_dens_add k X p σ D _ _ _ (fun c => _root_.GlobalTheory.Mix.dens_update_tens k X p σ D L i A B c) f
  exact ⟨h.1 hA hB, h.2 (h.1 hA hB) hA hB⟩

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadraticStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  first | (exact @GlobalTheory.AV.AbVar.pull_zsmul_of_symm) | (exact GlobalTheory.AV.AbVar.pull_zsmul_of_symm) | (intros; apply GlobalTheory.AV.AbVar.pull_zsmul_of_symm  <;> assumption)
end

