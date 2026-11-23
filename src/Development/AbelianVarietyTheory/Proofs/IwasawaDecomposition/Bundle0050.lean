module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Lin

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimplePart_mul_eq {f s N : End ℂ V} {c : ℂ} (hc : Commute f s) (hs : s.IsSemisimple)
    (hn : IsNilpotent (f - s)) (h : f * N = c • (N * f)) : s * N = c • (N * s) := by
  have key : ∀ (μ : ℂ) (k : ℕ), (f - (c * μ) • (1 : End ℂ V)) ^ k * N =
      c ^ k • (N * (f - μ • (1 : End ℂ V)) ^ k) := by
    intro μ k
    have h1 : (f - (c * μ) • (1 : End ℂ V)) * N = c • (N * (f - μ • (1 : End ℂ V))) := by
      rw [sub_mul, h, mul_sub, smul_sub]
      simp [smul_smul]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h1, smul_mul_assoc, smul_smul,
        mul_assoc, ← pow_succ', ← pow_succ]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [End.iSup_maxGenEigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    have h1 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hv hc
      hs.isFinitelySemisimple hn
    have h2 : N v ∈ f.maxGenEigenspace (c * μ) := by
      rw [End.mem_maxGenEigenspace] at hv ⊢
      obtain ⟨k, hk⟩ := hv
      refine ⟨k, ?_⟩
      have := LinearMap.congr_fun (key μ k) v
      simpa [hk] using this
    have h3 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil h2 hc
      hs.isFinitelySemisimple hn
    simp [h1, h3, smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Lin

theorem isNilpotent_pow_sub_one {R : Type*} [Ring R] {u : R} (hu : IsNilpotent (u - 1)) (k : ℕ) :
    IsNilpotent (u ^ k - 1) := by
  rw [← mul_geom_sum]
  refine Commute.isNilpotent_mul_right ?_ hu
  exact Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)

theorem commute_of_commute_pow {R : Type*} [Ring R] [Algebra ℂ R] {u : Rˣ} {T : R} {m : ℕ}
    (hm : 0 < m) (hu : IsNilpotent ((u : R) - 1)) (h : Commute ((u : R) ^ m) T) :
    Commute (u : R) T := by
  set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL
  set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM
  have hLM : Commute L M := LinearMap.commute_mulLeft_right _ _
  have hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1) := by
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ)) := by simp [sub_mul]
    rw [this]
    refine (Commute.isNilpotent_mul_right ?_ hu).neg
    exact (Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)
  have hL1 : IsNilpotent (L - 1) := by
    have : L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1) := by ext; simp [hL, sub_mul]
    rw [this]; exact (LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu
  have hM1 : IsNilpotent (M - 1) := by
    have : M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1) := by ext; simp [hM, mul_sub]
    rw [this]; exact (LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'
  have hU : IsNilpotent (L * M - 1) := by
    have : L * M - 1 = (L - 1) * M + (M - 1) := by noncomm_ring
    rw [this]
    have c1 : Commute (L - 1) M := hLM.sub_left (Commute.one_left _)
    refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1
    exact (c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)
  set U := L * M with hUdef
  have hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i) := by
    have e : ∑ i ∈ Finset.range m, U ^ i =
        algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_
      exact (((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
    · exact (IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _
    · exact Algebra.commute_algebraMap_right _ _
  have h1 : (U ^ m - 1) T = 0 := by
    rw [hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, End.one_apply]
    rw [← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, inv_pow]
    simp
  rw [← geom_sum_mul, End.mul_apply] at h1
  have h2 : (U - 1) T = 0 := by
    have := ((End.isUnit_iff _).mp hsum).1
    exact this (by rw [h1, map_zero])
  have h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T := by
    simpa [hUdef, hL, hM, sub_eq_zero] using h2
  calc (u : R) * T = (u : R) * (T * (u⁻¹ : Rˣ)) * u := by simp [mul_assoc]
    _ = T * u := by rw [h3]

theorem exists_frobenius_semisimplification : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V) (N : End ℂ V), IsSmooth ρ → IsNilpotent N → (∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) → ∃ (a : WDRep h V) (u : (End ℂ V)ˣ), a.N = N ∧ IsNilpotent ((u : End ℂ V) - 1) ∧ Commute (u : End ℂ V) N ∧ (∀ σ, Commute (u : End ℂ V) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ V)ˣ) : End ℂ V) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ := End.exists_isNilpotent_isSemisimple (f := ρ (frob (h := h)))
  set f := ρ (frob (h := h)) with hfdef
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : f - s = n := by rw [hf]; simp
  have hns : Commute n s := by rw [← hsub]; exact hfs.sub_left (Commute.refl s)
  have hfu : IsUnit f := (Group.isUnit (frob (h := h))).map ρ
  have hsu : IsUnit s := by
    have : s = f + -n := by rw [← hsub]; simp
    rw [this]
    exact hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left
  obtain ⟨S, rfl⟩ := hsu
  obtain ⟨F, hF⟩ := hfu
  have hFS : Commute F S := by
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)
  set u : (End ℂ V)ˣ := S⁻¹ * F with hu
  have huS : Commute u S := (Commute.refl S).inv_left.mul_left hFS
  have hSu : S * u = F := by simp [hu]
  have hSu' : (S : End ℂ V) * u = f := by rw [← Units.val_mul, hSu, hF]
  have huS' : Commute (u : End ℂ V) (S : End ℂ V) := huS.units_val
  have hunil : IsNilpotent ((u : End ℂ V) - 1) := by
    have : (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ) := by
      rw [hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]; simp
    rw [this]
    exact hns.units_inv_right.isNilpotent_mul_right hnil
  have huN : Commute (u : End ℂ V) N := by
    have h1 := hc (frob (h := h))
    have h2 := semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1
    have hq : ((normV w : ℕ) : ℂ) ^ deg (frob (h := h)) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
    have h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u) := by
      rw [← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']
    exact (Units.mul_right_inj S).mp h3
  have huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, e⟩ := _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ (frob (h := h)) (τ * frob (h := h) * τ⁻¹) (by simp)
    have c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m) := by
      rw [one_smul]
      conv_lhs => rw [hfdef, e]
      rw [hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]
      simp
    have epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m := by
      rw [← huS'.symm.mul_pow, hSu']
    have c2 := semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by
      have : f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m := by
        rw [epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]
      rw [this]
      exact ((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right
        (isNilpotent_pow_sub_one hunil m)) c1
    rw [one_smul] at c1 c2
    refine commute_of_commute_pow hm hunil ?_
    have h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) =
        (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m) := by
      rw [Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]
    exact (Units.mul_right_inj _).mp h3
  let ρ' : Representation ℂ (Weil h) V :=
    { toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)
      map_one' := by simp
      map_mul' := fun σ τ => by
        have := ((huρ τ).units_zpow_left (-deg σ)).eq
        rw [map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }
  have hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) := fun _ => rfl
  have hsm : IsSmooth ρ' := .of_open hρ (by simp) fun σ hσ => by
    have : ρ (ineIncl h σ) = 1 := hσ
    rw [hρ', this]; simp
  have hfr : ρ' (frob (h := h)) = S := by
    rw [hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]; simp
  refine ⟨⟨ρ', N, hsm, _root_.GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob E Ω A w h V ρ' hsm (frob (h := h)) deg_frob (hfr ▸ hss), hN,
    fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩
  · rw [hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc,
      mul_assoc]
  · show _ = ρ' σ * _
    rw [hρ', mul_assoc, ← Units.val_mul, ← zpow_add]; simp

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivialStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_lift_of_residual_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A → (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) → ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  first | exact @GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | exact GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | (intros; apply GlobalTheory.InertiaLift.exists_mem_Ine_eq_on <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalDualEqAddSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LocalDualBase

theorem localDual_eq_add_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL _
  subst hJ
  have hform1 : ∀ x y : Fin n → E, hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun t => ⟨0, ?_⟩⟩
    have : (t - (0 : intV E w) • (0 : latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin 0) (Fin 0) E) L)))).1 = 0 :=
      Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

  set R := w.adicCompletion F
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl : l.1 + 1 = n := by simp [l]; omega
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  obtain ⟨pb, hpb⟩ := hσO p
  have hpb0 : (algebraMap (𝓞 E) E pb) ≠ 0 := by
    rw [hpb]
    intro h
    exact hp (by simpa using (map_eq_zero σ).1 h)
  set e0 : Fin n → E := Pi.single l (algebraMap (𝓞 E) E pb)⁻¹ with he0def
  have he0 : e0 ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L := by
    intro x hx
    rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [e0, hb]) (by simp)]
    obtain ⟨r, hr, hd⟩ := (hL x).1 hx l
    obtain ⟨s, rfl⟩ := hd hl
    obtain ⟨u, hu⟩ := hσO s
    refine ⟨u, ?_⟩
    rw [hu, hr]
    simp only [e0, Pi.single_eq_same]
    push_cast
    rw [map_mul, ← hpb]
    field_simp
  have hglob : ∀ y ∈ Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L),
      ∃ r : 𝓞 E, y - (algebraMap (𝓞 E) E r) • e0 ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      have hxl : Pi.single l (p : E) ∈ L := by
        refine (hL _).2 fun i => ?_
        by_cases h : i = l
        · subst h
          exact ⟨p, by simp, fun _ => dvd_rfl⟩
        · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
      have h1 := hy _ hxl
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)] at h1
      simp only [Pi.single_eq_same] at h1
      obtain ⟨r, hr⟩ := h1
      refine ⟨r, (hL _).2 fun j => ?_⟩
      by_cases hj : j = l
      · subst hj
        refine ⟨0, ?_, fun _ => dvd_zero _⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, hr, ← hpb]
        push_cast
        field_simp
        ring
      · have hxj : Pi.single j (1 : E) ∈ L := by
          refine (hL _).2 fun i => ?_
          by_cases h : i = j
          · subst h
            exact ⟨1, by simp, fun hi => absurd (Fin.ext (by omega)) hj⟩
          · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
        have h2 := hy _ hxj
        rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at h2
        simp only [Pi.single_eq_same, map_one, one_mul] at h2
        obtain ⟨u, hu⟩ := h2
        refine ⟨u, ?_, fun hj' => absurd (Fin.ext (by omega)) hj⟩
        simp [e0, hj, hu]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨r1, hr1⟩ := h1
      obtain ⟨r2, hr2⟩ := h2
      refine ⟨r1 + r2, ?_⟩
      have : y + z - (algebraMap (𝓞 E) E (r1 + r2)) • e0 =
          (y - (algebraMap (𝓞 E) E r1) • e0) + (z - (algebraMap (𝓞 E) E r2) • e0) := by
        rw [map_add (f := _), add_smul]; abel
      rw [this]
      exact L.add_mem hr1 hr2
    | smul c y _ h =>
      obtain ⟨r, hr⟩ := h
      refine ⟨c * r, ?_⟩
      have : c • y - (algebraMap (𝓞 E) E (c * r)) • e0 = c • (y - (algebraMap (𝓞 E) E r) • e0) := by
        ext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul]
        simp only [Algebra.smul_def]
        ring
      rw [this]
      exact L.smul_mem c hr
  have hincl : ∀ r : 𝓞 E, inclE (F := F) R (algebraMap (𝓞 E) E r) ∈ intV E w := by
    intro r
    exact Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)
  refine ⟨⟨fun i => inclE (F := F) R (e0 i),
    Submodule.subset_span ⟨e0, Submodule.subset_span he0, rfl⟩⟩, fun t => ?_⟩
  obtain ⟨t, ht⟩ := t
  suffices H : ∃ s : intV E w, t - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) ∈
      latS (F := F) R (intV E w) L by
    obtain ⟨s, hs⟩ := H
    exact ⟨s, hs⟩
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨r, hr⟩ := hglob y' hy'
    refine ⟨⟨_, hincl r⟩, ?_⟩
    have : (fun i => inclE (F := F) R (y' i)) - inclE (F := F) R (algebraMap (𝓞 E) E r) •
        (fun i => inclE (F := F) R (e0 i)) =
        fun i => inclE (F := F) R ((y' - (algebraMap (𝓞 E) E r) • e0) i) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
    rw [this]
    exact Submodule.subset_span ⟨_, hr, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    refine ⟨s1 + s2, ?_⟩
    have : x + y - ((s1 + s2 : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        (x - (s1 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) +
        (y - (s2 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hs1 hs2
  | smul a x _ h =>
    obtain ⟨s, hs⟩ := h
    refine ⟨a * s, ?_⟩
    have : a • x - ((a * s : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        a • (x - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_mul, mul_smul, smul_sub]
      rfl
    rw [this]
    exact Submodule.smul_mem _ a hs

end GlobalTheory.Mem.LocalDualBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_localValues_global_over_places_above : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  first | exact @GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | exact GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | (intros; apply GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm <;> assumption)
end

