module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualSelmerClassFromCoeffsKilledByMul
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.DualSub

section Cup

variable {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M']
  [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M'] {n : ℕ}
  (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)


omit [TopologicalSpace M] [DiscreteTopology M] in
theorem cupB_left (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x x' : Γ → M) (y : Γ → M') (w : M)
    (hy : Continuous y) (hy' : ∀ g h, y (g * h) = y g + π' g (y h)) (hx : ∀ g, x' g = x g + (π g w - w))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x' y := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P w (y g), hF.add (((IsLocallyConstant.iff_continuous y).2 hy).comp fun m => P w m), fun g k => ?_⟩
  have h1 := h g k
  simp only [hx, map_add (f := _), map_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, Pi.add_apply, hy', hP] at h1 ⊢
  linear_combination h1

theorem cupB_right (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add (f := _), map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

end Cup

theorem exists_compLeft {A Y Y' : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {r : ℕ}
    (e : Y →ₗ[A] Y') (m : Fin r → Y') (h : ∀ a, m a ∈ LinearMap.range e) : ∃ m', e.compLeft (Fin r) m' = m := by
  choose m' hm' using h
  exact ⟨m', funext hm'⟩

theorem dualSel_of_smul_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (Y₂' : Type) [AddCommGroup Y₂'] [Module A Y₂'] [TopologicalSpace Y₂'] [DiscreteTopology Y₂'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))) (β₂ : Y₂ →+ Y₂' →+ ZMod (X.l i ^ (nu X i + 1))) (f : Y →ₗ[A] Y₂) (e : Y₂' →ₗ[A] Y') (c t : A), Bal A β → Bal A β₂ → Function.Surjective f → Function.Injective e → (∀ y', (c * t) • y' = 0 → y' ∈ LinearMap.range e) → (∀ y y', β₂ (f y) y' = β y (e y')) → (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y' g m = m) → t • m = 0) → ∀ y : Z1 (repOn ρ κ⁻¹ Y'), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ Y') (fun g => c • y.1 g) → ∃ y₂ : Z1 (repOn ρ κ⁻¹ Y₂'), DualSel bkP i s κ ρ β₂ Q y₂ ∧ Cob (repOn ρ κ⁻¹ Y') (fun g a => y.1 g a - e (y₂.1 g a)) := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y _ _ _ _ Y' _ _ _ _ Y₂ _ _ _ _ Y₂' _ _ _ _ β β₂ f e c t hβ hβ₂ hf he hct
    hfe ht y hy hc
  obtain ⟨hcY, hcY', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ
  obtain ⟨-, -, hP₂, -⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y₂ Y₂' β₂ hβ₂
  obtain ⟨m, hm⟩ := hc
  have hE : Function.Injective (e.compLeft (Fin D.R.r)) := fun a b hab => funext fun j => he (congrFun hab j)

  have hq := hNI (Y' ⧸ LinearMap.range (c • (LinearMap.id : Y' →ₗ[A] Y')))
    ((Submodule.mkQ _).compLeft (Fin D.R.r) m) fun g => by
      rw [← repOn_map, ← sub_eq_zero, ← map_sub, ← hm g]
      funext a
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y.1 g a, rfl⟩
  obtain ⟨m', hm'⟩ := exists_compLeft (c • (LinearMap.id : Y' →ₗ[A] Y')) m fun a =>
    (Submodule.Quotient.mk_eq_zero _).1 (congrFun hq a)
  have hm'' : m = c • m' := hm'.symm
  have hcm : Continuous fun g => repOn ρ κ⁻¹ Y' g m' := hcY'.comp (continuous_id.prodMk continuous_const)
  have hkill : ∀ g, c • (y.1 g - (repOn ρ κ⁻¹ Y' g m' - m')) = 0 := fun g => by
    have := hm g
    simp only at this
    rw [smul_sub, this, hm'', map_smul, smul_sub, sub_self]
  have hex : ∀ g, ∃ z, e.compLeft (Fin D.R.r) z = y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') := fun g =>
    exists_compLeft e _ fun a => hct _ (by
      rw [mul_comm, mul_smul]
      have := congrFun (hkill g) a
      rw [Pi.smul_apply] at this
      rw [this, Pi.zero_apply, smul_zero])
  choose z hz using hex
  have hzc : Continuous z := by
    have h1 : IsLocallyConstant fun g => y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') :=
      (IsLocallyConstant.iff_continuous _).2 (y.2.1.sub (hcm.sub continuous_const))
    exact (IsLocallyConstant.iff_continuous _).1 (IsLocallyConstant.desc z (e.compLeft (Fin D.R.r))
      (by rw [show (e.compLeft (Fin D.R.r)) ∘ z = _ from funext hz]; exact h1) hE)
  have hzz : ∀ g h, z (g * h) = z g + repOn ρ κ⁻¹ Y₂' g (z h) := fun g h => hE (by
    rw [map_add (f := _), repOn_map, hz, hz, hz, y.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel)
  refine ⟨⟨z, hzc, hzz⟩, ⟨fun v h1 h2 h3 τ hτ => hE ?_, fun v hv => ?_, fun v hv x₂ hx₂ => ?_⟩, m', fun g => ?_⟩
  · show e.compLeft _ (z τ) = _
    rw [hz, hy.1 v h1 h2 h3 τ hτ, (hU v h1 h2 h3 _ (N.plOm.2 v) τ hτ).2]
    simp
  · obtain ⟨m₀, hm₀⟩ := hy.2.1 v hv
    have h1 := ht v hv (c • (m₀ - m')) fun g hg => by
      have := hkill g
      rw [hm₀ g hg] at this
      rw [map_smul, map_sub, ← sub_eq_zero, ← smul_sub, ← this]
      congr 1
      abel
    obtain ⟨m₂, hm₂⟩ := exists_compLeft e (m₀ - m') fun a => hct _ (by
      rw [mul_comm, mul_smul]
      exact congrFun h1 a)
    refine ⟨m₂, fun g hg => hE ?_⟩
    show e.compLeft _ (z g) = _
    rw [hz, map_sub, repOn_map, hm₂, hm₀ g hg, map_sub]
    abel
  · obtain ⟨xc, hxc, hxe⟩ := _root_.GlobalTheory.NewPrime.bkOn_le_map_of_surjective D N X bkP i s A κ Q hS hK Y Y₂ f hf v hx₂
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xc
    have h1 := hy.2.2 v hv x hxc
    have h2 := cupB_right _ ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype)
      (vecPair D.R.r β) (fun g => hP g.1) x.1 _ (fun g => e.compLeft _ (z g.1)) m' x.2.1 x.2.2
      (hcm.comp continuous_subtype_val) (fun g => hz g.1) h1
    have h3 : (Submodule.Quotient.mk x₂ : H1 _) = Submodule.Quotient.mk (cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r))
        continuous_of_discreteTopology (fun g m => repOn_map (Tgl i s) κ f g.1 m) x) := hxe.symm
    obtain ⟨w, hw⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h3)
    refine cupB_left _ ((repOn (Tgl i s) κ Y₂).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y₂').comp (DecV N v).subtype)
      (vecPair D.R.r β₂) (fun g => hP₂ g.1) (fun g => f.compLeft _ (x.1 g)) x₂.1 (fun g => z g.1) w
      (hzc.comp continuous_subtype_val) (fun g h => hzz g.1 h.1) (fun g => ?_) ?_
    · rw [← hw g]
      exact (add_sub_cancel _ _).symm
    · obtain ⟨F, hF, h2⟩ := h2
      refine ⟨F, hF, fun g h => ?_⟩
      rw [← h2 g h]
      show vecPair _ β₂ _ (repOn ρ κ⁻¹ Y₂' g.1 (z h.1)) = vecPair _ β _ (repOn ρ κ⁻¹ Y' g.1 (e.compLeft _ (z h.1)))
      rw [← repOn_map, vecPair_apply, vecPair_apply]
      exact Finset.sum_congr rfl fun a _ => hfe _ _
  · have : (fun a => y.1 g a - e (z g a)) = y.1 g - e.compLeft _ (z g) := rfl
    show (fun a => y.1 g a - e (z g a)) = _
    rw [this, hz, sub_sub_cancel]

end GlobalTheory.DualSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SepFil

variable {l : ℕ} [Fact l.Prime]

theorem ev_eq_zero_iff_pt {e : Per.Fl l} (he : GlobalTheory.MemLoc.IsEps e) (m : ℕ) (y : Per.BdRp l) :
    Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y := by
  have hk := _root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he
  obtain ⟨-, hθ, hu, -, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  have hfil := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e he).1 1
  have hx : GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e)) := by
    rw [GlobalTheory.MemLoc.aDp, RingHom.comp_apply]
  have hmem : ∀ (n : ℕ) (a : Per.AinfP l), a ∈ Per.kerP l ^ n ↔
      algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n ∣ a := by
    intro n a
    rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hback : ∀ (n : ℕ) (w : Per.BdRp l), GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n ∣ w → Per.ev l n w = 0 := by
    rintro n w ⟨z, rfl⟩
    rw [map_mul, hx, ← map_pow (algebraMap (Per.AinfP l) (Per.BdRp l)), GlobalTheory.MemLoc.CrisUnique.ev_alg,
      Ideal.Quotient.eq_zero_iff_mem.2 ((hmem n _).2 dvd_rfl), zero_mul]
  have hnu : ¬ IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e)) := by
    intro h
    have h1 := (hθ _).2 ((hfil (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e))).2 (by rw [pow_one]))
    exact (h.map (Per.θD l)).ne_zero h1
  have hone : ∀ w : Per.BdRp l, Per.ev l 1 w = 0 → GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ∣ w := by
    intro w hw
    by_cases h0 : Per.θD l w = 0
    · have h1 := (hfil w).1 ((hθ w).1 h0)
      rwa [pow_one] at h1
    · exfalso
      have h1 := (hu w h0).map (Per.ev l 1)
      rw [hw, isUnit_zero_iff, eq_comm, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)),
        Ideal.Quotient.eq_zero_iff_mem, hmem, pow_one] at h1
      apply hnu
      rw [hx]
      exact (isUnit_of_dvd_one h1).map _
  have hdense : ∀ (n : ℕ) (w : Per.BdRp l), ∃ (a : Per.AinfP l) (z : Per.BdRp l),
      w = algebraMap (Per.AinfP l) (Per.BdRp l) a + GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n * z := by
    intro n w
    induction n with
    | zero => exact ⟨0, w, by rw [map_zero, pow_zero, one_mul, zero_add]⟩
    | succ n ih =>
      obtain ⟨a, z, hz⟩ := ih
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 z)
      obtain ⟨z', hz'⟩ := hone (z - algebraMap (Per.AinfP l) (Per.BdRp l) b) (by
        rw [map_sub, GlobalTheory.MemLoc.CrisUnique.ev_alg, hb, sub_self])
      refine ⟨a + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n * b, z', ?_⟩
      rw [map_add (f := _), map_mul, map_pow, ← hx, pow_succ, mul_assoc, ← hz', hz]
      ring
  refine ⟨fun hy ↦ ?_, hback m y⟩
  obtain ⟨a, z, hz⟩ := hdense m y
  have h1 := hback m _ (dvd_mul_right (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m) z)
  rw [hz, map_add (f := _), h1, add_zero, GlobalTheory.MemLoc.CrisUnique.ev_alg, Ideal.Quotient.eq_zero_iff_mem, hmem] at hy
  rw [hz]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [hx, ← map_pow]
  exact map_dvd _ hy

theorem dvd_of_forall_near {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ)
    (c : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (a : Ainf l) (z : Per.BdRp l),
      c - (l : Per.BdRp l) ^ r * GlobalTheory.MemLoc.aDp l a = GlobalTheory.MemLoc.aDp l d ^ m * z) :
    GlobalTheory.MemLoc.aDp l d ^ m ∣ c := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.CrisUnique.exists_isEps l
  have hk := GlobalTheory.MemLoc.ker_theta_eq_span_xi he
  have hxd : GlobalTheory.MemLoc.xi e ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hk, ← hd]
    exact Ideal.mem_span_singleton_self d
  have hdx : d ∣ GlobalTheory.MemLoc.xi e := by
    rw [← Ideal.mem_span_singleton, hd, hk]
    exact Ideal.mem_span_singleton_self _
  have hev : ∀ y : Per.BdRp l, Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y :=
    ev_eq_zero_iff_pt he m
  have h0 : Per.ev l m c = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r ↦ ?_
    obtain ⟨a, z, hz⟩ := h r
    refine ⟨a, ?_⟩
    have h1 : Per.ev l m (GlobalTheory.MemLoc.aDp l d ^ m * z) = 0 :=
      (hev _).2 (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (map_dvd _ hxd) m) z)
    rw [← hz, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast,
      GlobalTheory.MemLoc.CrisUnique.ev_aDp] at h1
    exact h1
  exact (pow_dvd_pow_of_dvd (map_dvd _ hdx) m).trans ((hev c).1 h0)

end GlobalTheory.BKReal.SepFil

namespace GlobalTheory.BKReal.SepFil

theorem dvd_of_forall_near_OD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O),
    (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) →
    ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m w h
  have hE : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  set d := ϖ.ev 1 (eis l 1 e) with hd_def
  have hd : Ideal.span {d} = RingHom.ker (Per.θ l) := ϖ.span_ev_eis 1
  have hξ : ϖ.iAl O K (EIn l e _) ^ m = (1 : O) ⊗ₜ[ℤ_[l]] (GlobalTheory.MemLoc.aDp l d ^ m) := by
    rw [hE, Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  rw [hξ] at h ⊢
  let b := Module.Free.chooseBasis ℤ_[l] O
  have key : ∀ i, GlobalTheory.MemLoc.aDp l d ^ m ∣ GlobalTheory.Decompl.crd b i w := by
    intro i
    refine dvd_of_forall_near hd m _ fun r ↦ ?_
    obtain ⟨y, z, hz⟩ := h r
    refine ⟨GlobalTheory.Decompl.crd b i y, GlobalTheory.Decompl.crd b i z, ?_⟩
    have h1 := congrArg (GlobalTheory.Decompl.crd b i) hz
    have h2 : GlobalTheory.Decompl.crd b i (toOD l O y) = GlobalTheory.MemLoc.aDp l (GlobalTheory.Decompl.crd b i y) :=
      GlobalTheory.Decompl.crd_map b (ainfToBdRp l) i y
    rw [LinearMap.map_sub, ← Nat.cast_pow, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_mul, h2,
      Nat.cast_pow] at h1
    exact h1
  choose c hc using key
  refine ⟨∑ j, b j ⊗ₜ[ℤ_[l]] c j, GlobalTheory.Decompl.ext_crd b fun i ↦ ?_⟩
  rw [GlobalTheory.Decompl.crd_mul, GlobalTheory.Decompl.crd_sum, ← hc i]

end GlobalTheory.BKReal.SepFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_of_dvd_restrict_discS : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  intro l _ K bk ρ h0 h1 R hR y hy
  obtain ⟨q, k, r, hr, e⟩ := _root_.GlobalTheory.BSP.WDiv.weierstrass_div l K bk ρ h0 h1 y
  have e' := congrArg R e
  rw [map_mul, map_add (f := _), map_mul, hR.ext, hR.ext, RingHom.id_apply, RingHom.id_apply] at e'
  have hd : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) := by
    have h2 := hy.mul_left (R (((l : ℕ) : bk.DS ρ) ^ k))
    rw [e'] at h2
    exact (dvd_add_right (dvd_mul_right _ _)).1 h2
  have hr0 := _root_.GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk r hr hd
  rw [hr0, Polynomial.coe_zero, map_zero, add_zero] at e
  exact ((isUnit_l_disc l (X : bk.S) ρ).pow k).dvd_mul_left.1 ⟨q, e⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatExact

theorem W_exact : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π hses
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  exact ⟨h1, h3, fun x => h2 x⟩

end GlobalTheory.LatExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockAction
section
noncomputable section

namespace GlobalTheory.SpanBlockAction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section

variable {O : Type} [CommRing O] {n r t : ℕ}

def ActsAs (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (M : Matrix (Fin n) (Fin n) O) (P : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Prop :=
  ∀ u, e ((M.map (toFr O)).mulVec u) =
    ((P.map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (d c) * (e u).2 c)

theorem map_smul_toFr {k : ℕ} (c : O) (M : Matrix (Fin k) (Fin k) O) :
    (c • M).map (toFr O) = toFr O c • M.map (toFr O) := by
  ext i j
  simp [smul_eq_mul]

theorem map_sum_toFr {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) O) :
    (∑ i, M i).map (toFr O) = ∑ i, (M i).map (toFr O) := by
  ext i j
  simp [Matrix.sum_apply]

private theorem sum_mulVec_eq {K : Type} [CommRing K] {k m : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (∑ i, A i).mulVec v = ∑ i, (A i).mulVec v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem smul_mulVec_eq' {K : Type} [CommRing K] {k : ℕ} (a : K) (A : Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (a • A).mulVec v = a • A.mulVec v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem actsAs_sum
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    {m : ℕ} (c : Fin m → O) (M : Fin m → Matrix (Fin n) (Fin n) O) (P : Fin m → Matrix (Fin r) (Fin r) O)
    (d : Fin m → Fin t → O) (h : ∀ k, ActsAs e (M k) (P k) (d k)) :
    ActsAs e (∑ k, c k • M k) (∑ k, c k • P k) (fun j => ∑ k, c k * d k j) := by
  unfold ActsAs at h ⊢
  intro u
  rw [map_sum_toFr, map_sum_toFr]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul_toFr, sum_mulVec_eq, smul_mulVec_eq', map_sum, map_smul, h]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Algebra.smul_def]

theorem ActsAs.unique
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    {M : Matrix (Fin n) (Fin n) O} {P P' : Matrix (Fin r) (Fin r) O} {d d' : Fin t → O}
    (h : ActsAs e M P d) (h' : ActsAs e M P' d') : P = P' := by
  have hv : ∀ v : Fin r → FractionRing O, (P.map (toFr O)).mulVec v = (P'.map (toFr O)).mulVec v := by
    intro v
    have h1 := h (e.symm (v, 0))
    have h2 := h' (e.symm (v, 0))
    rw [h1] at h2
    simpa using congrArg Prod.fst h2
  have hm : P.map (toFr O) = P'.map (toFr O) := by
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v
  ext i j
  apply IsFractionRing.injective O (FractionRing O)
  have := congrFun (congrFun hm i) j
  simpa [toFr] using this

end

theorem actsAs_mat {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    {σ : Γ →* GL (Fin n) O} {ρ : Γ →* GL (Fin r) O} {χ : ℕ → (Γ →* Oˣ)}
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    (h : IsDecomp (t := t) σ ρ χ e) (g : Γ) :
    ActsAs e (mat σ g) (mat ρ g) (fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)) := by
  unfold ActsAs
  intro u
  simpa [overK, matRep, mapM, mat] using h g u

theorem exists_block_action {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ))
    (π : X)
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (hspan : Submodule.span O (Set.range (mat ρ)) = ⊤) (hdec : IsDecomp (t := t) (rep π) ρ χ e) :
    ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O)
      (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O),
      (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) =
        (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧
      ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  classical
  have hact : ∀ M ∈ Submodule.span O (Set.range (mat (rep π))),
      ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e M p.1 p.2 := by
    intro M hM
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.mp hM
    have hg : ∀ k, ∃ γ, mat (rep π) γ = (g k : Matrix (Fin n) (Fin n) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), ?_⟩
    have := actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
      (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
    simpa only [hγ] using this
  refine ⟨fun a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.1 else 0,
    fun j a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.2 j else 0, ?_, ?_⟩
  · intro a ha u
    have hex := hact (a π) (eval_mem_span ha π)
    simp only [dif_pos hex]
    exact hex.choose_spec u
  · intro P
    have hP : P ∈ Submodule.span O (Set.range (mat ρ)) := hspan ▸ Submodule.mem_top
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hP
    have hg : ∀ k, ∃ γ, mat ρ γ = (g k : Matrix (Fin r) (Fin r) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨∑ k, c k • (fun x => mat (rep x) (γ k)), ?_, ?_⟩
    · exact inRing_sum _ fun k _ => inRing_smul (c k) (inRing_mat (γ k))
    · have hev : (∑ k, c k • (fun x => mat (rep x) (γ k))) π = ∑ k, c k • mat (rep π) (γ k) := by
        simp [Finset.sum_apply]
      have hA : ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) (∑ k, c k • mat ρ (γ k))
          (fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) := by
        rw [hev]
        exact actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
          (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
      have hex : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O),
          ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) p.1 p.2 :=
        ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), hA⟩
      simp only [dif_pos hex]
      rw [ActsAs.unique hex.choose_spec hA, ← hsum]
      simp only [hγ]

end GlobalTheory.SpanBlockAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJumpStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystallineLetter_of_hodgeJump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  first | exact @GlobalTheory.NL.JumpVec.exists_letter_of_jump | exact GlobalTheory.NL.JumpVec.exists_letter_of_jump | (intros; apply GlobalTheory.NL.JumpVec.exists_letter_of_jump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocyclesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_normal_subgroup_two_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), ∀ h ∈ L, bform (X := X) x.1 y.1 h ≠ 0 → ∃ U : Subgroup (GE N), IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧ (∀ g ∈ L, x.1 g = 0 → x.1 (cConj X g) = 0 → y.1 g = 0 → y.1 (cConj X g) = 0 → g ∈ U) ∧ ∀ σ g : GE N, g * σ * g⁻¹ * h⁻¹ ∈ U → bform (X := X) x.1 y.1 σ ≠ 0 := by
  first | exact @GlobalTheory.CocycleKernel.exists_open_normal | exact GlobalTheory.CocycleKernel.exists_open_normal | (intros; apply GlobalTheory.CocycleKernel.exists_open_normal <;> assumption)
end

