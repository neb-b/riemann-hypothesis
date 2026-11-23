module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfIota
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtFixed
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
theorem tameAnyAt_fixed_alt_alt : ∀ D : D7, _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  intro D hA hF i π ρ hc hr hfull hρ k hk v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨ι, hinj, hred⟩ := _root_.GlobalTheory.TypeLeaf.exists_redVia D i k hk
  have hpol := _root_.GlobalTheory.IneAway.ineAt' D hA hF i π ρ hc hr hfull hρ k v _ rfl (tameAnyFix_not_over D i k hk v) _ (D.ntypes.tg_mem k v)
  have hlab := D.ntypes.inertiaCharpoly_type k v _ (_root_.UpperTheory.GalS.fl0' hfull k v)
  rw [← tameAnyFix_isoLoc D π, hlab] at hpol
  have h1 := hred _ _ hpol
  have hchar : Matrix.charpoly ((redF D i ρ (D.nd.gam0 i (D.naut.plGw k v)) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D [⟨D.R.r, π, 1⟩] k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ (1 : ℤ))).prod := by
    rw [D.ntypes.heckeLoc_gamma_places]
    simp only [zpow_one, tameAnyFix_map_primeToPart]
    rw [← h1, ← Matrix.charpoly_map]
    rfl
  have hval : ∀ y : Fb (D.host.g k) (D.host.g_prime k),
      iotaO D.nd D.naut i (chi1 D.nd i (D.ntypes.tg k v)) = D.ntypes.teichC k y →
      D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i (D.naut.plGw k v)))) = ι y := by
    intro y hy
    have h2 := hred (X - C (chi1 D.nd i (D.ntypes.tg k v))) {y} (by simp [hy])
    rw [D.ntypes.heckeLoc_gamma_places]
    simpa using h2
  rcases D.ntypes.chiT_tg i k v hk with h | h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, 1, Or.inl rfl, Or.inl rfl, hinj, hchar, ?_⟩
    rw [zpow_one, tameAnyFix_map_primeToPart]
    exact hval _ h
  · refine ⟨v, ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, ι, 1, -1, Or.inl rfl, Or.inr rfl, hinj, hchar, ?_⟩
    rw [zpow_neg_one, tameAnyFix_map_primeToPart, hval _ h]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameFixedOfType
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
theorem tame_fixed_of_type_alt : ∀ D : D7, WildOne D → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  intro D hW hG hF i π ρ hc ha hfull hρ k hl v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.nd.l i).Prime := D.nd.lPrime i
  have hw := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hine := _root_.GlobalTheory.IneAway.ineAt' D hG hF i π ρ hc ha hfull hρ k v _ rfl hw
  obtain ⟨ι, hι, hred⟩ := _root_.GlobalTheory.TypeLeaf.exists_redVia D i k hl
  have hf := _root_.UpperTheory.GalS.fl0' hfull k v
  unfold labSig at hf ⊢
  rw [isoLoc_single] at hf ⊢
  refine ⟨ι, hι, ?_, ?_⟩
  · have h1 := (hine _ (D.ntypes.tg_mem k v)).trans (D.ntypes.inertiaCharpoly_type k v _ hf)
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x => X - C (D.ntypes.teichC k x)).prod at h1
    change _ = ((rts (k := k) (v := v) (D.naut.locG π _)).map fun x =>
      X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod
    set m := rts (k := k) (v := v) (D.naut.locG π _) with hm
    have hne : ∀ x ∈ m, x ≠ 0 := by
      rintro x hx rfl
      have h2 : (X : ℂ[X]) ∣ (m.map fun x => X - C (D.ntypes.teichC k x)).prod := by
        refine Multiset.dvd_prod (Multiset.mem_map.2 ⟨0, hx, ?_⟩)
        rw [teich_zero _ (D.ntypes.teichC_inj k), map_zero, sub_zero]
      rw [← h1, ← Matrix.charpoly_map, X_dvd_iff] at h2
      have h3 := Matrix.det_eq_sign_charpoly_coeff
        (((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaO D.nd D.naut i))
      rw [h2, mul_zero] at h3
      exact (Matrix.GeneralLinearGroup.map (iotaO D.nd D.naut i) (ρ (D.ntypes.tg k v))).det_ne_zero h3
    rw [charpoly_redF, hred _ m h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [map_primeToPart ι (isOfFinOrder_of_ne_zero (hne x hx))]
  · obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 (D.naut.plGw k v))
    rw [normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)] at hφ
    refine ⟨φ, ?_⟩
    set t := D.ntypes.tg k v with ht
    have hu := wild_of_frob (D.ntypes.tg_mem k v) hφ
    have huI : (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (D.ntypes.tg_mem k v) _))
        (conj_mem_Ine hφ.1 (D.ntypes.tg_mem k v))
    set u := (t ^ D.host.g k)⁻¹ * (φ * t * φ⁻¹) with hudef
    have h1 := (hine u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hg : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := _root_.GlobalTheory.WildKill.eq_one_of_wild_of_unipotent _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hg _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    rw [hudef, map_mul, map_inv, inv_mul_eq_one, map_pow] at h3
    exact h3.symm
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TheoremThreePrimeHolds
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem theorem_three_prime_holds_alt_alt (D : D7) : _root_.Formalism.MainNotions.AdmissibleThreePrime.ThreePrimeTheoremStatement D := by
  rintro ⟨hT, hG⟩ hBB i Sig ⟨x, hx⟩ hdz hgood
  have hcusp := cusp_of D hT i x Sig hx hgood
  refine ⟨hcusp, fun ρ hρ => ?_⟩
  have hG' := _root_.UpperTheory.GalS.g3p' hG i Sig ⟨x, hx⟩ hdz (fun k v => (hgood k).1.2.1 v) hcusp ρ hρ
  have hfact : ∀ j : Fin 2, Fact (D.host.g j).Prime := fun j => ⟨D.host.g_prime j⟩
  have hBB' : Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hBB
  have hne : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) → D.nd.l i ≠ D.host.g k :=
    fun k hk h => hk (Or.inl h)
  have key : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
      Formalism.CyclotomicNorms.IrredOn (redF D i ρ) ⊤ ∧
      (∀ (H : Subgroup (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) [H.Normal], Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ H) →
        Group.IsSolvable (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ H) → (∀ v, D.ntypes.tg k v ∈ H) →
        Formalism.CyclotomicNorms.IrredOn (redF D i ρ) H) := by
    intro k hk
    have hA := (hG' k (hne k hk)).1
    choose ι hι using hA
    choose φ hφ using fun v => (hι v).2.2
    have T := Formalism.CyclotomicNorms.irreducibility_of_good_tuple D.R.r D.host.g D.nd.PlG (Fin D.R.m)
      (fun j v => D.naut.items₂ j (D.naut.plGw j v) (isoLoc D.nd D.naut Sig (D.naut.plGw j v)))
      D.nd.chiT hBB' (fun j => (hgood j).1) (D.nd.l i) k hk (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (redF D i ρ)
      (fun v => D.ntypes.tg k v) φ ι hφ (fun v => (hι v).1) (fun v => (hι v).2.1)
    exact ⟨T.1, T.2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)
    · have h1 : D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := fun h1 => by
        have hm : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := ⟨h0, h1⟩
        rw [hBB'] at hm
        exact hm
      exact (key 1 h1).1
    · exact (key 0 h0).1
  · intro k hk Hs _ hopen hsolv hIne
    have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ Hs) := Subgroup.quotient_finite_of_isOpen Hs hopen
    exact (key k hk).2 Hs inferInstance hsolv
      (fun v => hIne _ (D.naut.plGw_over k v) (D.ntypes.tg_mem k v))
  · intro k hk w hw hTG
    obtain ⟨v, j, ι, e₁, e₂, he₁, he₂, hinj, hcp, hchi⟩ := (hG' k hk).2 w hw hTG
    show ¬ (Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)))).IsRoot _
    rw [hcp, hchi]
    exact not_root_of hk (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
      (D.nd.chiT k) (hgood k).1 (hgood k).2 v j ι hinj e₁ e₂ he₁ he₂
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiOverO
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie
  GlobalTheory.SplitRead GlobalTheory.XiOver Formalism.L2.Host
theorem xi_over_o_of_adm2 (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (T : Formalism.L2.Host.NCharTied D C nch Tp) (V : Formalism.L2.Host.ValLL0 D C) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut)
    (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : ChebSplit D.nd) : XiOverO D.nd D.naut := by
  intro i
  obtain ⟨ρ, hρ, hwd, -⟩ := (_root_.UpperTheory.GalS.weak' h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)
  have hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w) := fun w hw => by
    rw [hwd w hw]
    exact (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  have hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
        {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by
    intro w hw B σ hB hσ
    have e := D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1
      ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))
    rw [ha, charpoly_fin_one] at e
    simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at e
    have e2 := C_injective (sub_right_injective e)
    rw [← hwd w hw, ha]
    exact congrArg _ e2.symm
  let d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Qbar (D.nd.l i) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    fun g => Matrix.det_fin_one _
  have hd : Continuous d := by
    have : (d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g =>
        ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := funext hde
    rw [this]
    exact (continuous_apply_apply 0 0).comp hρ
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero
  have hS : closure {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ := by
    have hd := (h5 hfin.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_char D.nd D.naut i d hd _ hS (by
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨x, hx⟩ := frob_value D C nch Tp T V w
    have e := hfrob w hw B σ hB hσ
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde] at e
    exact ⟨_, (D.naut.iotaQC i).injective e⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩
  · have h1 := (D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ
    apply Units.ext
    apply iota_inj D.nd D.naut i
    rw [hξ, hde, h1]
    simp
  · rw [hfrob w hw B σ hB hσ, ← hde, ← hξ]
    rfl
end
end GlobalTheory.ResLoc
end
end
end

