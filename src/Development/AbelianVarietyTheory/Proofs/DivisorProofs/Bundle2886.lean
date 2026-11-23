module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePart
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.BotClassDict GlobalTheory.NormSum.VacInt

variable {D : D7}

theorem idem_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D w ε') (hv : v ≠ w) : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, k1, k0⟩ := h'
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext _ fun u => ?_)
  change α u * α' u = 0
  by_cases hu : u = v
  · subst hu
    exact (congrArg (α u * ·) (k0 u hv)).trans (mul_zero _)
  · exact (congrArg (· * α' u) (h0 u hu)).trans (zero_mul _)

theorem cut_mul_cut {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {e f : R} (h : e * f = 0) (A : Matrix n n R) :
    (e • A + (1 - e • (1 : Matrix n n R))) * (f • A + (1 - f • (1 : Matrix n n R))) =
      (e + f) • A + (1 - (e + f) • (1 : Matrix n n R)) := by
  have h' : f * e = 0 := by rw [mul_comm, h]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub, smul_add,
    h, h', zero_smul, add_smul]
  abel

theorem mt_mul (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_prod (V : HSp D) (g : GA D V) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (L : List (HeightOneSpectrum (𝓞 D.host.F))) (hL : L.Nodup) :
    Formalism.L2.Theta.mt V (L.map fun v => GlobalTheory.VacStab.locPart V v g).prod =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • 1) := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, RingHom.map_zero, zero_smul, zero_smul, zero_add, sub_zero]
    rfl
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have h0 : ε v * (L.map ε).sum = 0 := by
      rw [← List.sum_map_mul_left]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact idem_orth (hε v) (hε w) fun e => hL.1 (e ▸ hw)
    rw [List.map_cons, List.prod_cons, mt_mul, GlobalTheory.VacStab.mt_locPart V (hε v), ih hL.2, List.map_cons, List.sum_cons,
      RingHom.map_add]
    exact cut_mul_cut (by rw [← RingHom.map_mul, h0, RingHom.map_zero]) _

theorem natCast_mem_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) : (q : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal ↔ (q : 𝓞 E) ∈ Q.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal ↔ _
  rw [map_natCast]

theorem finQ_sum_idem {q : ℕ} (hq : q.Prime) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    finQ D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (∑ v ∈ S, ε v)) = eps D.host.E fun p => p = q := by
  apply (GlobalTheory.BotFormula.toFinE D).injective
  refine FiniteAdeleRing.ext _ fun Q => ?_
  have hev : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (∑ v ∈ S, ε v).2 w = if w ∈ S then 1 else 0 := by
    intro w
    have e1 : (∑ v ∈ S, ε v).2 w = ∑ v ∈ S, evalV D.host.F w (sndA D.host.F (ε v)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_sum]
      rfl
    have e2 : ∀ v, evalV D.host.F w (sndA D.host.F (ε v)) = if w = v then 1 else 0 := by
      intro v
      obtain ⟨α, h, h1, h0⟩ := hε v
      rw [h]
      change evalV D.host.F w α = _
      split_ifs with hw
      · subst hw; exact h1
      · exact h0 w hw
    rw [e1, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_ite_eq]
  have hr : GlobalTheory.BotFormula.toFinE D (eps D.host.E fun p => p = q) Q =
      GlobalTheory.AdeleBaseChange.locMap ℚ Q (if pr (Q.under (𝓞 ℚ)) = q then 1 else 0) := by
    have := toFinE_tmul (D := D) 1 (idem fun p => p = q)
    rw [map_one, one_mul] at this
    refine (congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) this).trans ?_
    refine (GlobalTheory.AdeleBaseChange.adMap_apply _ Q).trans (congrArg _ ?_)
    rw [idem, mkInt_apply]
    congr
  have hiff : Q.under (𝓞 D.host.F) ∈ S ↔ pr (Q.under (𝓞 ℚ)) = q := by
    rw [hS, natCast_mem_under, ← Nat.prime_dvd_prime_iff_eq (pr_prime _) hq, pr_dvd_iff, natCast_mem_under]
  rw [GlobalTheory.ZeroAtPlaces.comp_base, hev, hr]
  by_cases h : Q.under (𝓞 D.host.F) ∈ S
  · rw [if_pos h, if_pos (hiff.1 h), map_one, map_one]
  · rw [if_neg h, if_neg (fun e => h (hiff.2 e)), map_zero, map_zero]

theorem exists_prod_eq_part : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  intro D V hG q hq g
  have hI : Ideal.span {(q : 𝓞 D.host.F)} ≠ ⊥ := by simpa using hq.ne_zero
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (Ideal.finite_factors hI).toFinset
  have hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal := fun v => by
    simp [S, Ideal.dvd_span_singleton]
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  refine ⟨S.toList.map fun v => GlobalTheory.VacStab.locPart V v g, ?_, ?_⟩
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hh
    exact ⟨v, ε v, hε v, (hS v).1 (Finset.mem_toList.1 hv), GlobalTheory.VacStab.suppPl_locPart V (hε v) g⟩
  · have hm := mt_prod V g ε hε S.toList (Finset.nodup_toList S)
    rw [Finset.sum_map_toList] at hm
    have he := finQ_sum_idem hq S hS ε hε
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have h1 : finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact RingHom.map_one _
      · exact RingHom.map_zero _
    change finQ D (Formalism.L2.Theta.mt V _ i j) = eps D.host.E (fun p => p = q) * finQ D (Formalism.L2.Theta.mt V g i j) +
      (1 - eps D.host.E fun p => p = q) * (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j
    rw [hm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, he, h1, sub_mul, one_mul]

end GlobalTheory.PrimePart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGenIsoAndSchemeIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem gs_appLE {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ g ⁻¹ᵁ U) (hz : f z ∈ V) (x : Γ(X, U)) :
    gs f z V ((g.appLE U V h).hom x) = gs (f ≫ g) z U x := by
  have e : (g.appLE U V h).hom x = (Y.presheaf.map (homOfLE h).op).hom ((g.app U).hom x) := rfl
  rw [e, gs_res f z h hz, gs_pull f g z U (h hz)]

theorem exists_sec_of_genIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (π : X₁ ⟶ Y), π ≫ f₁ = 𝟙 X₁ → f₁ ≫ π = 𝟙 Y → ∀ (k : ℕ) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), ∃ σ' : SecM (𝟙 X₁) L₁ k, (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h1 h2 π hπ hπ' k s
  let ε : Fin 1 → ℤ := fun _ => (k : ℤ)
  let u := isoInv (ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε)
  have hu : u.IsGen := isoInv_isGen (ReciprocityTheory.ChartRestriction.G.DVR.flatIso_isGen L₁ L₂ f₁ f₂ w hw ε)
  let t := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso s hu (LB.isLB_linComb h1 (fun _ : Fin 1 => f₁) ε) (LB.isLB_linComb h2 (fun _ : Fin 1 => f₂) ε)
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t, ?_⟩
  intro y i j hy2 hy1

  have hyA : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) := Set.mem_iInter.2 fun _ => hy1
  have hyB : y ∈ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := Set.mem_iInter.2 fun _ => hy2
  have hyAB : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) ⊓ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := ⟨hyA, hyB⟩
  have hyw : y ∈ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hy2, Set.mem_iInter.2 fun _ => hy1⟩

  have s1 : gs f₁ y _ ((ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t).f fun _ => j) =
      gs (𝟙 Y) y _ (t.f fun _ => j) := by
    show gs f₁ y _ ((π.appLE _ _ _).hom _) = _
    rw [gs_appLE f₁ π y _ (show f₁ y ∈ _ from Set.mem_iInter.2 fun _ => by simpa using hy1), hπ']

  have s2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) := by
    rw [← ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec s hu _ _ (fun _ => j) (fun _ => i)]
    exact (gs_res (𝟙 Y) y inf_le_left hyAB _).symm

  have s3 : gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) =
      ((gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j))) ^ (-(k : ℤ))).val * gs (𝟙 Y) y _ (s.f fun _ => i) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand
    rw [gs_mul (𝟙 Y) y _ hyAB, gs_unit (𝟙 Y) y _ hyAB, gs_res (𝟙 Y) y inf_le_right hyAB]
    congr 2
    rw [map_inv, gm_res (𝟙 Y) y _ hyAB]
    show (gm (𝟙 Y) y _ (res _ ((ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε).s ((fun _ => j), (fun _ => i))))⁻¹)⁻¹ = _
    have hyBA : y ∈ ((LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).div (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε)).U ((fun _ => i), (fun _ => j)) := ⟨hyB, hyA⟩
    have hyAB' : y ∈ ((LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).div (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε)).U ((fun _ => j), (fun _ => i)) := hyAB
    rw [map_inv, inv_inv]
    erw [gm_res (𝟙 Y) y _ hyBA]
    show gm (𝟙 Y) y _ (∏ q : Fin 1, res (ReciprocityTheory.ChartRestriction.G.DVR.flat_le L₁ L₂ f₁ f₂ ((fun _ => j), (fun _ => i)) q) (w.s (fun _ => i, fun _ => j)) ^ (-ε q)) = _
    rw [Fin.prod_univ_one]
    erw [map_zpow, gm_res (𝟙 Y) y _ hyAB']
    rfl
  rw [s1, s2, s3, gs_unit (𝟙 Y) y _ hyw, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.SecThroughIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGeneratingLineBundleIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_sec_of_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k),
    ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j →
        gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k *
          gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h₁ h₂ k σ'
  let t : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))) :=
    TG.pullSec' L₁ (fun _ => 𝟙 X₁) (fun _ => (k : ℤ)) σ' f₁ (fun _ => f₁) (fun _ => (Category.comp_id _).symm)
  refine ⟨secOfIso (u := flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _), ?_⟩
  intro y i j hi hj
  have hz : (𝟙 Y) y ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e := ps_gs_secOfIso (flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _)
    (fun _ => i) (fun _ => j) (𝟙 Y) y hz
  have hw' : (𝟙 Y) y ∈ ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e1 : gm (𝟙 Y) y _ ((flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))).s (fun _ => j, fun _ => i)) =
      gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ)) := by
    show gm (𝟙 Y) y _ (∏ k' : Fin 1, res (flat_le L₁ L₂ f₁ f₂ (fun _ => j, fun _ => i) k')
      (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ))) = _
    rw [map_prod, Fin.prod_univ_one, map_zpow]
    congr 1
    exact gm_res _ y _ (show (𝟙 Y) y ∈ LB.wchart L₁ (fun _ : Fin 1 => f₁) (fun _ => j) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) from ⟨hz.2, hz.1⟩) _
  have e2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs f₁ y _ (σ'.f fun _ => j) := by
    simp only [t]
    rw [TG.pullSec'_f]
    refine (gs_res _ y _ hz.2 _).trans ?_
    refine (gs_pull (𝟙 Y) f₁ y _ (Set.mem_iInter.2 fun _ => hj) _).trans ?_
    rw [Category.id_comp]
    rfl
  rw [e, e1, e2, gs_unit _ y _ hw', zpow_neg, inv_inv, zpow_natCast, Units.val_pow_eq_pow_val]

end GlobalTheory.SecThroughIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem val_pow_mul_eq {R : Type} [CommRing R] (t b : Rˣ) (a : R) (k : ℕ) :
    ((t ^ k : Rˣ) : R) * a = a * ((b⁻¹ ^ k : Rˣ) : R) * (((t * b) ^ k : Rˣ) : R) := by
  have e : ((b⁻¹ ^ k : Rˣ) : R) * ((b ^ k : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  rw [mul_pow, Units.val_mul]
  linear_combination (-(((t ^ k : Rˣ) : R) * a)) * e

theorem exists_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  intro X L hL Ω _ _ x g hg k σ
  obtain ⟨j₀, hj₀⟩ : ∃ i, ∀ p : Sp Ω, x.base p ∈ L.U i := by
    have hc : x.base (IsLocalRing.closedPoint Ω) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, fun p => ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open (L.U i).isOpen hi⟩
  have hW : (⊤ : (Sp Ω).Opens) ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  have hG : (⊤ : (Sp Ω).Opens) ≤ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  let ωs : Γ(Sp Ω, ⊤) := ((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)) *
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs, ?_⟩
  intro Z r z J hJ
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs) = ωs := by
    simp
  rw [hinv]
  have hj : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => J ((r ≫ x) ≫ 𝟙 X)) := hJ.mem _ (r ≫ x)
  have hj0 : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) := hW (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hgj : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => J (r ≫ x ≫ 𝟙 X)) := hJ.mem _ r
  have hg0 : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) := hG (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  rw [sval_of σ (r ≫ x) z J _ (fun _ => rfl), sec_trans σ (r ≫ x) z hj hj0, val_of g r z J _ (fun _ => rfl),
    gen_trans hg r z hgj hg0]
  have hT : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (r ≫ x) z (fun _ => J ((r ≫ x) ≫ 𝟙 X)) (fun _ => j₀) =
      trF (L := L) (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => 1) r z (fun _ => J (r ≫ x ≫ 𝟙 X)) (fun _ => j₀) ^ k := by
    simp only [trF]
    rw [Category.assoc]
    simp
  have hp := (gs_pull r x z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀)) hj0 (σ.f fun _ => j₀)).symm
  have hm : r z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have h1 := gs_mul r z ⊤ hm (((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)))
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  have h2 := gm_res r z hG hm (g.s fun _ => j₀)
  rw [gs_res r z hW hm, gs_unit r z ⊤ hm, map_pow, map_inv] at h1
  erw [h2] at h1
  rw [hT, hp, h1]
  exact val_pow_mul_eq _ _ _ _

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquareStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_thetaElement_level_four_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  first | exact @GlobalTheory.ThetaSquare.exists_symmetric_square | exact GlobalTheory.ThetaSquare.exists_symmetric_square | (intros; apply GlobalTheory.ThetaSquare.exists_symmetric_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg.BasisPull

theorem exists_basis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
  intro E _ _ _ H X t0 U R _ ρ t f hf φ n v hv hb
  let ψ : Γ(X, U.1) →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ
  have hx : spMap ψ ≫ chart U = chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) ≫ f := by
    rw [hf, ← Category.assoc]
    congr 1
    rw [chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hv' := fun i => GlobalTheory.LieMet.isTan_map ψ hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map ψ hx hv hb
  choose vR hvR1 hvR2 using fun i => GlobalTheory.ShFam.OpenReg.exists_lift φ
    (spMap (algebraMap Γ(Sp R, ⊤) (DualNumber Γ(Sp R, ⊤))) ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    (spMap (dualMap ψ) ≫ v i) (by rw [(hv' i).1, Category.assoc])
  refine ⟨vR, fun i => (GlobalTheory.ShFam.OpenReg.tan_iff φ rfl (hvR1 i)).1 (by rw [hvR2]; exact hv' i), fun w hw => ?_, hvR2⟩
  have e : (fun i => spMap (dualMap ψ) ≫ v i) = fun i => vR i ≫ φ.φ := funext fun i => (hvR2 i).symm
  have h := hb' (w ≫ φ.φ) ((GlobalTheory.ShFam.OpenReg.tan_iff φ rfl hw.1).2 hw)
  rw [e] at h
  exact (existsUnique_congr fun cf => GlobalTheory.ShFam.OpenReg.comb_iff φ rfl hvR1 cf hw.1).1 h

end GlobalTheory.LocReg.BasisPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentialsStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega,
        ∀ G : PDivGroup p k,
          (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧
          Function.Surjective (θ G) ∧
          (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
          (∀ (a : WittVector p k) m,
            θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
          ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
            θ G (T.map f m) = omegaMap G H f (θ H m) :=
  @GlobalTheory.Dieu.theta_exists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTwistedSumSignEveryMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaTwistedSum_sign_everyMember : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  first | exact @GlobalTheory.Poinc.Sep.twistAtEach_exists | exact GlobalTheory.Poinc.Sep.twistAtEach_exists | (intros; apply GlobalTheory.Poinc.Sep.twistAtEach_exists <;> assumption)
end

