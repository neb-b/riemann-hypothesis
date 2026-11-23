module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031

@[expose] public section

noncomputable section

namespace GlobalTheory.RowPar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Filter

theorem exists_ss {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) :
    ∃ r : Γ →* GL (Fin n) k, IsSSRep r ∧ ρ.ker ≤ r.ker ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin n) (Fin n) k).charpoly := by
  obtain ⟨s, hs⟩ := GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf (glRep (QuotientGroup.kerLift ρ))
  let t : (Γ ⧸ ρ.ker) →* GL (Fin n) k :=
    ((LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin n)).toAlgHom.toMonoidHom.comp s).toHomUnits
  have ht : ∀ x, (t x : Matrix (Fin n) (Fin n) k) = LinearMap.toMatrix' (s x) := fun _ => rfl
  have hv : ∀ x v, (t x : Matrix (Fin n) (Fin n) k).mulVec v = s x v := fun x v => by
    rw [ht, LinearMap.toMatrix'_mulVec]
  refine ⟨t.comp (QuotientGroup.mk' _), fun W hW => ?_, fun g hg => ?_, fun g => ?_⟩
  · obtain ⟨W', h1, h2⟩ := hs.1 W fun x v hx => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
      rw [← hv]
      exact hW g v hx
    exact ⟨W', fun g v hx => (hv _ v).symm ▸ h1 (QuotientGroup.mk' _ g) v hx, h2⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]
  · have h := GlobalTheory.SemisimplificationCharpoly.charpoly_eq _ _ hs (QuotientGroup.mk' _ g)
    rw [MonoidHom.comp_apply, ht, ← Matrix.charpoly_toLin', Matrix.toLin'_toMatrix', h]
    exact Matrix.charpoly_toLin' _

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

theorem eq_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    {f f' : G H.E N.Om → Y} (hf : Continuous f) (hf' : Continuous f')
    (h : ∀ᶠ w in cofinite, IsSplitPl H w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → f σ = f' σ) : f = f' := by
  obtain ⟨S, hS, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split H
  refine hC.eq_of_frob (hS.union (eventually_cofinite.1 h)) hf hf' fun v hv hd B hB σ hσ => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact hv.2 (hsp v hv.1 hd) B σ hB hσ

variable (A : NAut N)

variable {A}

section Residual

variable (A) (B₀ : what₂.places.Pl → ValuationSubring ℂ)
  (κ : ∀ w, B₀ w →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))

def IsRbar (σ : what₂.FT) (w : what₂.places.Pl)
    (r : G H.E N.Om →* GL (Fin R.r) (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))) : Prop :=
  IsSSRep r ∧ IsOpen (r.ker : Set (G H.E N.Om)) ∧ ∃ i Sig, HasParamW N A i σ Sig ∧
    ∀ᶠ v in cofinite, IsSplitPl H v → ∀ (B : ValuationSubring N.Om) (s : G H.E N.Om),
      IsPlaceOver (F := H.E) B v → IsFrob (F := H.E) B (normV v) s →
      ∃ p : (B₀ w)[X], p.map (B₀ w).subtype = galPol A (A.lpTw (isoLoc N A Sig v) ((1 - (R.r : ℝ)) / 2)) ∧
        (r s : Matrix (Fin R.r) (Fin R.r) _).charpoly = p.map (κ w)


variable {A B₀ κ}

end Residual

variable (A)

def FrobFam (i : N.Loc) (f : PlE H → ℂ[X]) : Prop :=
  ∃ F : Qbar (N.l i) → G H.E N.Om → Qbar (N.l i), (∀ z, Continuous (F z)) ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ → ∀ z, A.iotaQC i (F z σ) = (f w).eval (A.iotaQC i z)

variable {A}

theorem FrobFam.congr {i : N.Loc} {f f' : PlE H → ℂ[X]} (h : FrobFam A i f) (e : ∀ᶠ w in cofinite, f w = f' w) :
    FrobFam A i f' := by
  obtain ⟨F, h1, h2⟩ := h
  exact ⟨F, h1, (h2.and e).mono fun w hw => hw.2 ▸ hw.1⟩

theorem FrobFam.one (i : N.Loc) : FrobFam A i fun _ => 1 :=
  ⟨fun _ _ => 1, fun _ => continuous_const, Eventually.of_forall fun _ _ _ _ _ _ => by simp⟩

theorem FrobFam.mul {i : N.Loc} {f f' : PlE H → ℂ[X]} (h : FrobFam A i f) (h' : FrobFam A i f') :
    FrobFam A i fun w => f w * f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  refine ⟨fun z σ => F z σ * F' z σ, fun z => (h1 z).mul (h1' z), (h2.and h2').mono fun w hw B σ hB hσ z => ?_⟩
  rw [map_mul, hw.1 B σ hB hσ, hw.2 B σ hB hσ, eval_mul]

theorem FrobFam.eq_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) {i : N.Loc} {f f' : PlE H → ℂ[X]}
    (h : FrobFam A i f) (h' : FrobFam A i f') (e : ∀ᶠ w in cofinite, IsSplitPl H w → f w = f' w) :
    ∀ᶠ w in cofinite, f w = f' w := by
  obtain ⟨F, h1, h2⟩ := h
  obtain ⟨F', h1', h2'⟩ := h'
  have hF : ∀ z, F z = F' z := fun z => GlobalTheory.RowPar.eq_of_split hC (h1 z) (h1' z) <| by
    filter_upwards [h2, h2', e] with w a a' b hw B σ hB hσ
    apply (A.iotaQC i).injective
    rw [a B σ hB hσ, a' B σ hB hσ, b hw]
  filter_upwards [h2, h2'] with w a a'
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 w)
  refine Polynomial.funext fun z => ?_
  obtain ⟨z, rfl⟩ := (A.iotaQC i).surjective z
  rw [← a _ σ (N.plOm.2 w) hσ, ← a' _ σ (N.plOm.2 w) hσ, hF]

theorem frobFam_cusp (hG : GlobalTheory.GalOfCusp.Reading A) (i : N.Loc) {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hπ : A.csd π)
    (s : ℝ) (hs : GlobalTheory.GalOfCusp.RegAlgShift A π s) :
    FrobFam A i fun w => galPol A (A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)) := by
  obtain ⟨r, hr⟩ := hG i a ha π hπ s hs
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (Fact.out : (N.l i).Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  refine ⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.eval z, fun z => ?_, ?_⟩
  · simp only [Matrix.eval_charpoly]
    exact (continuous_const.sub hr.cont).matrix_det
  · filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hB hσ z
    rw [← (hr.frob h1 h2).2 B σ hB hσ]
    exact (eval_map_apply (A.iotaQC i).toRingHom _).symm

open GlobalTheory.RowTie

variable (A) in
theorem twSum_unr (L : List ((Σ a : ℕ, A.CG a) × ℝ)) : ∀ᶠ w in cofinite, ∀ p ∈ L, A.unr (A.locG p.1.2 w) :=
  (eventually_all_finite L.finite_toSet).2 fun p _ => A.locG_unr_ae p.1.2

theorem frobEig_twSum {L : List ((Σ a : ℕ, A.CG a) × ℝ)} {w : PlE H} (h : ∀ p ∈ L, A.unr (A.locG p.1.2 w)) :
    A.unr (twSum N A L w) ∧
      A.frobEig (twSum N A L w) = (L.map fun p => A.frobEig (A.lpTw (A.locG p.1.2 w) p.2)).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons p L ih =>
    have h1 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have h2 := (A.unr_tw _ p.2).2 (h p List.mem_cons_self)
    exact ⟨(A.unr_sum _ _).2 ⟨h2, h1.1⟩, by
      rw [List.map_cons, List.sum_cons, ← h1.2]; exact A.frobEig_sum _ _ h2 h1.1⟩

theorem frobFam_twSum (hG : GlobalTheory.GalOfCusp.Reading A) (i : N.Loc) (u : ℝ) (L : List ((Σ a : ℕ, A.CG a) × ℝ))
    (hL : ∀ p ∈ L, 1 ≤ p.1.1 ∧ A.csd p.1.2 ∧ GlobalTheory.GalOfCusp.RegAlgShift A p.1.2 (p.2 + u - (1 - (p.1.1 : ℝ)) / 2)) :
    FrobFam A i fun w => galPol A (A.lpTw (twSum N A L w) u) := by
  induction L with
  | nil =>
    refine (FrobFam.one i).congr (Eventually.of_forall fun w => ?_)
    simp [galPol, twSum, A.frobEig_tw _ u (A.lpZero_unr w), A.frobEig_zero]
  | cons p L ih =>
    obtain ⟨h1, h2, h3⟩ := hL p List.mem_cons_self
    refine ((frobFam_cusp hG i h1 _ h2 _ h3).mul (ih fun q hq => hL q (List.mem_cons_of_mem _ hq))).congr ?_
    filter_upwards [A.locG_unr_ae p.1.2, twSum_unr A L] with w a b
    change _ = galPol A (A.lpTw (A.lpSum (A.lpTw (A.locG p.1.2 w) p.2) (twSum N A L w)) u)
    rw [A.lpTw_sum, A.lpTw_add, sub_add_cancel, galPol, galPol, galPol,
      A.frobEig_sum _ _ ((A.unr_tw _ _).2 a) ((A.unr_tw _ _).2 (frobEig_twSum b).1), Multiset.map_add,
      Multiset.prod_add]

theorem eq_of_galPol {w : PlE H} {a b : A.LP w} (ha : A.unr a) (hb : A.unr b) {u : ℝ}
    (h : galPol A (A.lpTw a u) = galPol A (A.lpTw b u)) : a = b := by
  have h1 := congrArg Polynomial.roots h
  rw [galPol, galPol, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h1
  have h2 : A.lpTw a u = A.lpTw b u := by
    rw [A.unr_eq_lpUnr _ ((A.unr_tw a u).2 ha), h1, ← A.unr_eq_lpUnr _ ((A.unr_tw b u).2 hb)]
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using congrArg (A.lpTw · (-u)) h2


variable (A) in
def IsCohSum (n : ℕ) (Sig : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Sig, A.csd p.π) ∧ ∀ p ∈ Sig, ∀ τ, (A.infG p.π τ).Nodup ∧
    ∀ z ∈ A.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - (p.d : ℂ)) / 2

open GlobalTheory.SpehRigid in
theorem frobFam_isoLoc (hG : GlobalTheory.GalOfCusp.Reading A) (i : N.Loc) {n : ℕ} {Sig : List (Formalism.BasicNotions.Part A.CG)}
    (h0 : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) (h : IsCohSum A n Sig) :
    FrobFam A i fun w => galPol A (A.lpTw (isoLoc N A Sig w) ((1 - (n : ℝ)) / 2)) := by
  simp only [isoLoc_eq]
  refine frobFam_twSum hG i _ _ fun q hq => ?_
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
  refine ⟨(h0 p hp).1, h.1 p hp, fun τ => ⟨(h.2 p hp τ).1, fun z hz => ?_⟩⟩
  obtain ⟨m, rfl⟩ := (h.2 p hp τ).2 z hz
  exact ⟨m - k, by push_cast; ring⟩

theorem perm_of_split (hC : GlobalTheory.Published.ChebotarevDegreeOne) (hJ : IsobaricRigid N A) (hG : GlobalTheory.GalOfCusp.Reading A)
    (i : N.Loc) {n : ℕ} {Sig Sig' : List (Formalism.BasicNotions.Part A.CG)} (h0 : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d)
    (h0' : ∀ p ∈ Sig', 1 ≤ p.a ∧ 1 ≤ p.d) (h : IsCohSum A n Sig) (h' : IsCohSum A n Sig')
    (e : ∀ᶠ w in cofinite, IsSplitPl H w → isoLoc N A Sig w = isoLoc N A Sig' w) : Sig.Perm Sig' := by
  refine GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne R H what₂ N A hJ _ _
    (fun p hp => ⟨(h0 p hp).1, (h0 p hp).2, h.1 p hp⟩) (fun p hp => ⟨(h0' p hp).1, (h0' p hp).2, h'.1 p hp⟩) ?_
  filter_upwards [(frobFam_isoLoc hG i h0 h).eq_of_split hC (frobFam_isoLoc hG i h0' h')
    (e.mono fun w hw hs => by rw [hw hs]), twSum_unr A (Sig.flatMap (GlobalTheory.SpehRigid.flat N A)),
    twSum_unr A (Sig'.flatMap (GlobalTheory.SpehRigid.flat N A))] with w a b b'
  refine eq_of_galPol ?_ ?_ a
  · rw [GlobalTheory.SpehRigid.isoLoc_eq]; exact (frobEig_twSum b).1
  · rw [GlobalTheory.SpehRigid.isoLoc_eq]; exact (frobEig_twSum b').1

section Cusp

open GlobalTheory.CuspRep

variable [_root_.NumberField.IsTotallyComplex H.E]


variable (A) in
def ReadsCusp (e : ∀ a, A.CG a → CG H.E a) : Prop :=
  (∀ a, 1 ≤ a → Function.Injective (e a)) ∧ (∀ a π, 1 ≤ a → (e a π).IsUnitary) ∧
    ∀ a π w, 1 ≤ a → A.unr (A.locG π w) → ∃ B : Multiset ℂˣ, (e a π).HasSat w B ∧
      A.frobEig (A.locG π w) = B.map fun b => ((b⁻¹ : ℂˣ) : ℂ)

theorem hasSat_twist {a : ℕ} {π : CG H.E a} {w : PlE H} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {χ : Formalism.L2.Host.HChar H.E} (hχ : χ.UnrAt w) : (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem isobaricRigid_of_jacquetShalika (hJ : GlobalTheory.Published.JacquetShalikaRigidity) {e : ∀ a, A.CG a → CG H.E a}
    (he : ReadsCusp A e) : IsobaricRigid N A := by
  intro L L' hL hL' h
  let ν := GlobalTheory.HeckeGal.Model.absPow H.E
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E
  let Φ : ℂˣ → ℂ := fun b => ((b⁻¹ : ℂˣ) : ℂ)
  have hΦ : Function.Injective Φ := Units.val_injective.comp inv_injective
  have key : ∀ (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H), (∀ p ∈ L, 1 ≤ p.1.1) →
      (∀ p ∈ L, A.unr (A.locG p.1.2 w)) → ∃ B : Fin L.length → Multiset ℂˣ,
        (∀ j, ((e _ (L.get j).1.2).twist (ν (L.get j).2)).HasSat w (B j)) ∧
          (∑ j, B j).map Φ = A.frobEig (twSum N A L w) := by
    intro L w h1 h2
    choose B hB hB' using fun j : Fin L.length =>
      he.2.2 _ (L.get j).1.2 w (h1 _ (List.get_mem _ _)) (h2 _ (List.get_mem _ _))
    refine ⟨_, fun j => hasSat_twist (hB j) ((hν _).1 w), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(frobEig_twSum h2).2, ← Multiset.coe_mapAddMonoidHom, map_sum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Eq.trans ?_ (A.frobEig_tw _ (L.get j).2 (h2 _ (List.get_mem _ _))).symm
    rw [hB', Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Φ, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, ν, (hν _).2.1 w,
      Complex.cpow_neg, inv_inv]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨s, hs⟩ := hJ.unitary (fun j : Fin L.length => e _ (L.get j).1.2) (fun j : Fin L'.length => e _ (L'.get j).1.2)
    (fun j => hL _ (List.get_mem _ _)) (fun j => hL' _ (List.get_mem _ _))
    (fun j => he.2.1 _ _ (hL _ (List.get_mem _ _))) (fun j => he.2.1 _ _ (hL' _ (List.get_mem _ _))) ν hν
    (fun j => (L.get j).2) (fun j => (L'.get j).2) (by
      filter_upwards [h, twSum_unr A L, twSum_unr A L'] with w a b b'
      obtain ⟨B, h1, h2⟩ := key L w hL b
      obtain ⟨B', h1', h2'⟩ := key L' w hL' b'
      exact ⟨B, B', h1, h1', Multiset.map_injective hΦ (by rw [h2, h2', a])⟩)
  have inj : ∀ p q : Σ a : ℕ, A.CG a, 1 ≤ p.1 → (⟨p.1, e _ p.2⟩ : Σ a, CG H.E a) = ⟨q.1, e _ q.2⟩ → p = q := by
    rintro ⟨a, π⟩ ⟨b, π'⟩ ha h
    obtain rfl : a = b := (Sigma.mk.inj h).1
    exact congrArg _ (he.1 a ha (eq_of_heq (Sigma.mk.inj h).2))
  have e' : ∀ L : List ((Σ a : ℕ, A.CG a) × ℝ), (L : Multiset _) = Finset.univ.val.map L.get := fun L => by
    rw [Fin.univ_val_map, List.ofFn_get]
  rw [← Multiset.coe_eq_coe, e', e', ← Finset.map_univ_equiv s, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun j _ => Prod.ext (inj _ _ (hL _ (List.get_mem _ _)) (hs j).1) (hs j).2

end Cusp

variable (A)


variable {A}

variable (A)

def IsPar (Sig : List (Formalism.BasicNotions.Part A.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧ rankIso N A Sig = R.r ∧
  ∀ k v, (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).Monic ∧
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = R.r

def Par : Type := {Sig // IsPar A Sig}

def locPar (σ : Par A) (w : PlE H) : A.LP w := isoLoc N A σ.1 w

theorem lpDim_twSum (L : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    A.lpDim (twSum N A L w) = (L.map fun p => p.1.1).sum := by
  induction L with
  | nil => exact A.lpDim_zero w
  | cons p L ih =>
    refine (A.lpDim_sum _ _).trans (congrArg₂ (· + ·) ?_ ih)
    rw [A.lpDim_tw, A.locG_dim]

theorem lpDim_isoLoc (Sig : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A Sig w) = rankIso N A Sig := by
  induction Sig with
  | nil => exact A.lpDim_zero w
  | cons p L ih =>
    refine (A.lpDim_sum _ _).trans (congrArg₂ (· + ·) ?_ ih)
    rw [GlobalTheory.SpehRigid.spehLoc_eq, lpDim_twSum, GlobalTheory.SpehRigid.flat, List.map_map]
    simp [Function.comp_def, mul_comm]


structure Spec (M : Type) [AddCommGroup M] [Module ℂ M] where

  I : Type

  tp : I → Submodule ℂ M

  loc : I → ∀ w, A.LP w

  sat : I → PlE H → Multiset ℂ

  inf : (H.E →+* ℂ) → Multiset ℂ

namespace Spec

variable {A} {M : Type} [AddCommGroup M] [Module ℂ M] (S S' : Spec A M)


end Spec

variable {A} (S : ∀ μ j, Spec A (what₂.Mt μ j)) (T : ∀ μ, Spec A (what₂.Amb μ)) (c : what₂.Tup → ℕ → A.CG 1)


variable (B₀ : what₂.places.Pl → ValuationSubring ℂ)
  (κ : ∀ w, B₀ w →+* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))

variable {S c}

end GlobalTheory.RowPar

end
