module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.SenAdd

section
variable {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

theorem pow_mem (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (m : ℕ) :
    ∀ y ∈ Q, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Q.sub_mem (hQ y hy) (Q.smul_mem _ hy)

theorem mem_gen (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (y : A) :
    y ∈ (⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m)) ↔
      ∃ m : ℕ, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  have hm : Monotone fun m : ℕ => Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) := by
    refine monotone_nat_of_le_succ fun m z hz => ?_
    rw [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]
    simpa using pow_mem T Q hQ x 1 _ hz
  exact Submodule.mem_iSup_of_directed _ hm.directed_le

theorem pow_comm (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B) (hT : ∀ y, h (T y) = T' (h y))
    (x : k) (m : ℕ) (y : A) :
    h (((T - algebraMap k (Module.End k A) x) ^ m) y) = ((T' - algebraMap k (Module.End k B) x) ^ m) (h y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp [Module.algebraMap_end_apply, hT]

theorem gmult_transport (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B)
    (hT : ∀ y, h (T y) = T' (h y)) (P Q : Submodule k A) (P' Q' : Submodule k B)
    (hP : ∀ y ∈ P, T y ∈ P) (hQP : Q ≤ P) (hQ' : ∀ y ∈ Q', T' y ∈ Q')
    (hmap : ∀ y ∈ P, h y ∈ P') (hker : ∀ y ∈ P, h y ∈ Q' ↔ y ∈ Q)
    (hsur : ∀ z ∈ P', ∃ y ∈ P, z - h y ∈ Q') (x : k) : gmult T P Q x = gmult T' P' Q' x := by
  have hQ : ∀ y ∈ Q, T y ∈ Q := fun y hy =>
    (hker _ (hP y (hQP hy))).1 (by rw [hT]; exact hQ' _ ((hker y (hQP hy)).2 hy))
  unfold gmult
  set G := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) with hG
  set G' := P' ⊓ ⨆ m : ℕ, Q'.comap ((T' - algebraMap k (Module.End k B) x) ^ m) with hG'
  have hGG : ∀ y ∈ G, h y ∈ G' := by
    rintro y ⟨hy, hy2⟩
    obtain ⟨m, hm⟩ := (mem_gen T Q hQ x y).1 hy2
    refine ⟨hmap y hy, (mem_gen T' Q' hQ' x _).2 ⟨m, ?_⟩⟩
    rw [← pow_comm T T' h hT]
    exact (hker _ (hQP hm)).2 hm
  let φ : G →ₗ[k] (G' ⧸ Q'.submoduleOf G') := (Q'.submoduleOf G').mkQ ∘ₗ h.restrict hGG
  have hk : Q.submoduleOf G = LinearMap.ker φ := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    change y ∈ Q ↔ Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hker y hy.1).symm
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, hy, hzy⟩ := hsur z hz.1
    obtain ⟨m, hm⟩ := (mem_gen T' Q' hQ' x z).1 hz.2
    have hyG : y ∈ G := by
      refine ⟨hy, (mem_gen T Q hQ x y).2 ⟨m, (hker _ (pow_mem T P hP x m y hy)).1 ?_⟩⟩
      rw [pow_comm T T' h hT]
      have := Q'.sub_mem hm (pow_mem T' Q' hQ' x m _ hzy)
      rwa [map_sub, sub_sub_cancel] at this
    refine ⟨⟨y, hyG⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [eq_comm, Submodule.Quotient.eq]
    exact hzy
  rw [hk]
  exact (φ.quotKerEquivOfSurjective hs).finrank_eq

end

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]


omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem sh_one_le (N : Submodule k⟦X⟧ V) : sh 1 N ≤ N := by
  have := sh_le_sh_of_le (zero_le_one' ℤ) N
  rwa [sh_zero_eq] at this

theorem nab_mem_sh_one {l : ℕ} (R : RingPG k l) (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V)
    (hN : CondC g N) : ∀ y ∈ sh 1 N, nab g y ∈ sh 1 N := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  have hv := vv_ne_zero k
  have h1 := hN z hz
  have h2 : g z ∈ N := by simpa using N.add_mem (sh_one_le N h1) hz
  have h3 : vv k ^ (1 : ℤ) • (κ • g z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem κ h2, rfl⟩
  have h4 : nab g (vv k ^ (1 : ℤ) • z) = (g z - z) - vv k ^ (1 : ℤ) • (κ • g z) := by
    rw [nab_apply_eq, zpow_one, hg, hκ, ← algebraMap_smul k⸨X⸩ κ, mul_smul, ← smul_sub, inv_smul_smul₀ hv,
      sub_smul, one_smul, smul_smul, mul_comm (vv k)]
    change g z - ((κ : k⸨X⸩) * vv k) • g z - z = g z - z - ((κ : k⸨X⸩) * vv k) • g z
    abel
  rw [h4]
  exact Submodule.sub_mem _ h1 h3


omit [IsScalarTower k k⸨X⸩ V] in
theorem finite_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    FiniteDimensional k (↥(N.restrictScalars k) ⧸
      ((sh 1 N).restrictScalars k).submoduleOf (N.restrictScalars k)) := by
  obtain ⟨s, hs⟩ := hN
  have hle : Submodule.span k (s : Set V) ≤ N.restrictScalars k :=
    Submodule.span_le.2 fun y hy => hs ▸ Submodule.subset_span hy
  have key : ∀ y ∈ N, ∃ z ∈ Submodule.span k (s : Set V), y - z ∈ sh 1 N := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨z, hz, h⟩ := hy
      obtain ⟨z', hz', h'⟩ := hy'
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      have := Submodule.add_mem _ h h'
      rwa [sub_add_sub_comm] at this
    | smul a y _ hy =>
      obtain ⟨z, hz, h⟩ := hy
      refine ⟨PowerSeries.constantCoeff a • z, Submodule.smul_mem _ _ hz, ?_⟩
      set t : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
      have ha : a = PowerSeries.X * t + algebraMap k k⟦X⟧ (PowerSeries.constantCoeff a) :=
        PowerSeries.eq_X_mul_shift_add_const a
      have h3 : vv k ^ (1 : ℤ) • (t • z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem t (hle hz), rfl⟩
      have h4 : vv k ^ (1 : ℤ) • (t • z) = (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [zpow_one, mul_smul, vv_eq_coe_X]
        exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) (t • z)
      have h5 : a • y - PowerSeries.constantCoeff a • z = a • (y - z) + (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [← algebraMap_smul k⟦X⟧ (PowerSeries.constantCoeff a) z, eq_sub_of_add_eq ha.symm, smul_sub, sub_smul]
        abel
      rw [h5]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h) (h4 ▸ h3)
  haveI : FiniteDimensional k (Submodule.span k (s : Set V)) := FiniteDimensional.span_finset k s
  refine Module.Finite.of_surjective (Submodule.mkQ _ ∘ₗ Submodule.inclusion hle) fun w => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨z, hz, h⟩ := key y hy
  refine ⟨⟨z, hz⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [eq_comm, Submodule.Quotient.eq]
  exact h

end

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] {U : Type} [AddCommGroup U] [Module k⸨X⸩ U] [Module k⟦X⟧ U] [Module k U] [IsScalarTower k⟦X⟧ k⸨X⸩ U] [IsScalarTower k k⸨X⸩ U] [IsScalarTower k k⟦X⟧ U] [FiniteDimensional k⸨X⸩ U] (gV : V →ₗ[k] V) (gW : W →ₗ[k] W) (gU : U →ₗ[k] U) (f : W →ₗ[k⸨X⸩] V) (p : V →ₗ[k⸨X⸩] U), Semi R.γ gV → Function.Injective f → Function.Surjective p → Function.Exact f p → (∀ x, f (gW x) = gV (f x)) → (∀ x, p (gV x) = gU (p x)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC gV N → ∀ x : k, sen gV N x = sen gW (N.comap (f.restrictScalars k⟦X⟧)) x + sen gU (N.map (p.restrictScalars k⟦X⟧)) x := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ U _ _ _ _ _ _ _ _ gV gW gU f p hg _ _ hex hf hp N hN hC x
  have hN1 := (condC_iff_nab_mem gV N).1 hC
  have hN2 := nab_mem_sh_one R gV hg N hC
  have nf : ∀ y, f (nab gW y) = nab gV (f y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hf]
  have np : ∀ y, p (nab gV y) = nab gU (p y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hp]
  set N' := N.map (p.restrictScalars k⟦X⟧) with hN'
  have hsh : ∀ u, u ∈ sh 1 N' ↔ ∃ y ∈ sh 1 N, p y = u := by
    intro u
    constructor
    · intro hu
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hu
      exact ⟨_, mem_sh_iff_exists.2 ⟨z, hz, rfl⟩, map_smul p _ _⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
      exact mem_sh_iff_exists.2 ⟨p z, ⟨z, hz, rfl⟩, (map_smul p _ _).symm⟩
  have hU : ∀ u ∈ sh 1 N', nab gU u ∈ sh 1 N' := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hsh u).1 hu
    exact (hsh _).2 ⟨_, hN2 y hy, np y⟩
  let Q : Submodule k V := N.restrictScalars k ⊓ ((sh 1 N').restrictScalars k).comap (p.restrictScalars k)
  have hQ : ∀ y, y ∈ Q ↔ y ∈ N ∧ p y ∈ sh 1 N' := fun _ => Iff.rfl
  have hadd := GlobalTheory.PhiGam.GmultAdd.main (nab gV) (N.restrictScalars k) Q ((sh 1 N).restrictScalars k)
    (fun y hy => (hQ y).2 ⟨sh_one_le N hy, (hsh _).2 ⟨y, hy, rfl⟩⟩) inf_le_left hN1
    (fun y hy => (hQ _).2 ⟨hN1 y hy.1, by rw [np]; exact hU _ hy.2⟩) hN2 (finite_quot N hN.1) x
  have e1 : gmult (nab gV) (N.restrictScalars k) Q x = sen gU N' x :=
    gmult_transport (nab gV) (nab gU) (p.restrictScalars k) np _ _ (N'.restrictScalars k)
      ((sh 1 N').restrictScalars k) hN1 inf_le_left hU
      (fun y hy => ⟨y, hy, rfl⟩) (fun y hy => ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩)
      (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩) x
  have e2 : sen gW (N.comap (f.restrictScalars k⟦X⟧)) x = gmult (nab gV) Q ((sh 1 N).restrictScalars k) x := by
    refine gmult_transport (nab gW) (nab gV) (f.restrictScalars k) nf _ _ _ _ ?_ (sh_one_le _) hN2 ?_ ?_ ?_ x
    · intro y hy
      change f (nab gW y) ∈ N
      rw [nf]
      exact hN1 _ hy
    · intro y hy
      refine (hQ _).2 ⟨hy, ?_⟩
      change p (f y) ∈ _
      rw [hex.apply_apply_eq_zero]
      exact Submodule.zero_mem _
    · intro y _
      change f y ∈ sh 1 N ↔ y ∈ sh 1 _
      rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]
      rfl
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := (hsh _).1 hz.2
      obtain ⟨w, hw⟩ := (hex (z - y)).1 (by rw [map_sub, hyz]; exact sub_self _)
      refine ⟨w, ?_, ?_⟩
      · change f w ∈ N
        rw [hw]
        exact N.sub_mem hz.1 (sh_one_le N hy)
      · change z - f w ∈ sh 1 N
        rwa [hw, sub_sub_cancel]
  rw [e2, ← e1, add_comm]
  exact hadd

end GlobalTheory.PhiGam.SenAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem integral_eq_zero_of_shift_mul {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (g : V → ℂ) (t : V) (z : ℂ) (hz : z ≠ 1)
    (h : ∀ x, g (x + t) = g x * z) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = (∫ x, g x ∂μ) * z := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + t) ∂μ := (integral_add_right_eq_self g t).symm
      _ = ∫ x, g x * z ∂μ := by simp only [h]
      _ = (∫ x, g x ∂μ) * z := integral_mul_const z g
  have h2 : (∫ x, g x ∂μ) * (1 - z) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hz

theorem exists_short_dot_eq {F : Type} [NormedField F] {r : ℕ} (x₀ : F) {ε : ℝ} (hε : 0 < ε) (b : Fin r → F)
    (hb : b ∉ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε)) :
    ∃ t : Fin r → F, ‖t‖ < ε ∧ t ⬝ᵥ b = x₀ := by
  have hR : 0 ≤ ‖x₀‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hb' : ‖x₀‖ / ε < ‖b‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hb
  obtain ⟨i, hi⟩ : ∃ i, ‖x₀‖ / ε < ‖b i‖ := by
    by_contra hcon
    push Not at hcon
    exact absurd ((pi_norm_le_iff_of_nonneg hR).2 hcon) (not_le.2 hb')
  have hbi : b i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hi
    exact absurd hi (not_lt.2 hR)
  refine ⟨Pi.single i (x₀ / b i), (pi_norm_lt_iff hε).2 fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, norm_div, div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hε] at hi
      calc ‖x₀‖ < ‖b j‖ * ε := hi
        _ = ε * ‖b j‖ := mul_comm _ _
    · rw [Pi.single_eq_of_ne hj, norm_zero]
      exact hε
  · rw [single_dotProduct, div_mul_cancel₀ _ hbi]

theorem fourG_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
    HasCompactSupport (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf' hU
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨U, hU0, hUinv⟩ := hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  have h00 : ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), (0 : Fin r → F), (0 : F)) = (0 : Gl r F) := rfl
  obtain ⟨ε2, hε2, hB⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  obtain ⟨ε3, hε3, hC⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  have key2 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε2 →
      f' (A, b + t, c, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hB t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  have key3 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε3 →
      f' (A, b, c + t, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hC t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  let P : Set (Matrix (Fin r) (Fin r) F × F) := (fun Y : Gl r F => (Y.1, Y.2.2.2)) '' tsupport f'
  have hPc : IsCompact P := hf'.2.image (by fun_prop)
  let K : Set (Gl r F) :=
    (fun p : (Matrix (Fin r) (Fin r) F × F) × (Fin r → F) × (Fin r → F) => ((p.1.1, p.2.1, p.2.2, p.1.2) : Gl r F)) ''
      (P ×ˢ (Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3) ×ˢ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)))
  have hKc : IsCompact K :=
    (hPc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image (by fun_prop)
  refine HasCompactSupport.intro hKc fun Y hY => ?_
  obtain ⟨A, b, c, l⟩ := Y
  show ∫ b', ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ ∂μ = 0
  by_cases hP : (A, l) ∈ P
  · by_cases hb : b ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3)
    · by_cases hc : c ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)
      · exact absurd ⟨((A, l), b, c), ⟨hP, hb, hc⟩, rfl⟩ hY
      · obtain ⟨t, ht, htc⟩ := exists_short_dot_eq x₀ hε2 c hc
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun b' => ?_
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
        simp only
        rw [key2 A b' c' l t ht, dotProduct_add, ← add_assoc, AddChar.map_add_eq_mul, dotProduct_comm c t, htc,
          mul_assoc]
    · obtain ⟨t, ht, htb⟩ := exists_short_dot_eq x₀ hε3 b hb
      have hin : ∀ b' : Fin r → F, ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ = 0 := by
        intro b'
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun c' => ?_
        rw [key3 A b' c' l t ht, add_dotProduct, add_right_comm, AddChar.map_add_eq_mul, htb, mul_assoc]
      simp only [hin, integral_zero]
  · have hz : ∀ b' c' : Fin r → F, f' (A, b', c', l) = 0 := by
      intro b' c'
      by_contra hne
      exact hP ⟨(A, b', c', l), subset_tsupport _ hne, rfl⟩
    simp only [hz, zero_mul, integral_zero]

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerEulerProductQuotientInjective
section
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem hasSum_inner_quotient_eulerProduct_injective : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) [DecidableEq ι] (c : ι → Γ →* Γ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (s : ι → ℝ) (e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}), (∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) → (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ g, a g = ∏ᶠ v, a (c v g)) → (∀ g, ‖B g‖ ≤ 1) → B 1 = 1 → (∀ g k, k ∈ K → B (g * k) = B g) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset Γ), (∀ g ∈ C, c v g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ s v) → (∀ v γ, HasSum (fun x : Γ ⧸ K.comap (c v) => a (c v (Quotient.out x)) • B (γ * c v (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap (c v), a (c v (Quotient.out x)) • B (c v (Quotient.out x)))) → ∃ W : H →L[ℂ] H, Function.Injective W ∧ ∀ x y, HasSum (fun q : Γ ⧸ K => a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ) ⟪x, W y⟫_ℂ := by
  intro Γ _ K ι _ c H _ _ _ a B s e he hK hidem horth haK ha1 hfac hB hB1 hBK hs hs1 hloc hstep
  classical
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H

  have aK : ∀ g : Γ, a ((QuotientGroup.mk g : Γ ⧸ K).out) = a g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]; exact haK g k k.2
  have BK : ∀ g : Γ, B ((QuotientGroup.mk g : Γ ⧸ K).out) = B g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]; exact hBK g k k.2
  have acv : ∀ v (g : Γ), a (c v ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)).out)) = a (c v g) := by
    intro v g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.comap (c v)) g
    rw [hk, map_mul]; exact haK _ _ k.2
  have cv1 : ∀ v, c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out) ∈ K := by
    intro v
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.comap (c v)) (1 : Γ)
    rw [hk, one_mul]; exact k.2
  let x0 : ∀ v, Γ ⧸ K.comap (c v) := fun v => QuotientGroup.mk 1
  let a' : ∀ v, Γ ⧸ K.comap (c v) → ℂ := fun v x => a (c v x.out)
  let Z : ι → (H →L[ℂ] H) := fun v => ∑' x : Γ ⧸ K.comap (c v), a (c v x.out) • B (c v x.out)
  let B' : (∀ v, Γ ⧸ K.comap (c v)) → (H →L[ℂ] H) := fun f =>
    if h : {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite then B ((e.symm ⟨f, h⟩).out) else B 1
  have B'eval : ∀ (f : ∀ v, Γ ⧸ K.comap (c v)) (g : Γ),
      (∀ w, f w = (QuotientGroup.mk g : Γ ⧸ K.comap (c w))) → B' f = B g := by
    intro f g hf
    have hfeq : f = (e (QuotientGroup.mk g)).1 := funext fun w => (hf w).trans (he g w).symm
    subst hfeq
    simp only [B', dif_pos (e (QuotientGroup.mk g)).2, Subtype.coe_eta, Equiv.symm_apply_apply]
    exact BK g
  have h1 : ∀ v, a' v (x0 v) = 1 := by
    intro v
    show a (c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out)) = 1
    rw [acv, map_one, ha1]
  have hfin : ∀ v (C : Finset (Γ ⧸ K.comap (c v))), x0 v ∉ C → ∑ x ∈ C, ‖a' v x‖ ≤ s v := by
    intro v C hC
    have eqcl : ∀ x y : Γ ⧸ K.comap (c v), (c v x.out)⁻¹ * c v y.out ∈ K → x = y := by
      intro x y hxy
      have hm : x.out⁻¹ * y.out ∈ K.comap (c v) := by
        rw [Subgroup.mem_comap, map_mul, map_inv]; exact hxy
      have := (QuotientGroup.eq (s := K.comap (c v))).mpr hm
      simpa only [QuotientGroup.out_eq'] using this
    calc ∑ x ∈ C, ‖a' v x‖ = ∑ g ∈ C.image (fun x => c v x.out), ‖a g‖ := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          apply eqcl
          have hxy' : c v x.out = c v y.out := hxy
          rw [hxy', inv_mul_cancel]; exact K.one_mem
      _ ≤ s v := by
          apply hloc
          · intro g hg
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
            refine ⟨hidem v _, fun hmem => hC ?_⟩
            have : x = x0 v := by
              apply eqcl
              exact K.mul_mem (K.inv_mem hmem) (cv1 v)
            rw [← this]; exact hx
          · intro g hg g' hg' hgg
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
            rw [eqcl x y hgg]
  have hnorm : ∀ f, ‖B' f‖ ≤ 1 := by
    intro f
    simp only [B']
    split_ifs
    · exact hB _
    · exact hB 1
  have hx0 : B' x0 = 1 := by
    rw [B'eval x0 1 (fun w => rfl), hB1]
  have hrec : ∀ v (f : ∀ v, Γ ⧸ K.comap (c v)), {w | f w ≠ x0 w}.Finite → f v = x0 v →
      HasSum (fun x => a' v x • B' (Function.update f v x)) (B' f * Z v) := by
    intro v f hf hv
    set γ' : Γ := (e.symm ⟨f, hf⟩).out with hγ'
    have hfγ' : ∀ w, f w = (QuotientGroup.mk γ' : Γ ⧸ K.comap (c w)) := by
      intro w
      have h2 : e (QuotientGroup.mk γ') = ⟨f, hf⟩ := by
        rw [hγ', QuotientGroup.out_eq', Equiv.apply_symm_apply]
      have h3 := congrArg (fun p => p.1 w) h2
      simp only at h3
      rw [← h3, he]
    set γ : Γ := γ' * (c v γ')⁻¹ with hγ
    have hcγ : c v γ = 1 := by
      rw [hγ, map_mul, map_inv, hidem, mul_inv_cancel]
    have key : ∀ x : Γ ⧸ K.comap (c v), B' (Function.update f v x) = B (γ * c v x.out) := by
      intro x
      apply B'eval
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [Function.update_self]
        refine ((QuotientGroup.eq (s := K.comap (c w))).mpr ?_).trans (QuotientGroup.out_eq' x) |>.symm
        rw [Subgroup.mem_comap]
        simp only [mul_inv_rev, map_mul, map_inv, hidem, hcγ, inv_one, mul_one, inv_mul_cancel]
        exact K.one_mem
      · rw [Function.update_of_ne hw, hfγ' w, QuotientGroup.eq, Subgroup.mem_comap]
        simp only [hγ, mul_inv_rev, inv_inv, map_mul, map_inv, horth v w _ hw.symm, inv_one, mul_one,
          one_mul, inv_mul_cancel]
        exact K.one_mem
    have hupd : Function.update f v (x0 v) = f := by
      rw [← hv]; exact Function.update_eq_self v f
    have hBf : B' f = B γ := by
      rw [← hupd, key, hBK _ _ (cv1 v)]
    rw [hBf]
    have := hstep v γ
    convert this using 1
    funext x
    rw [key]
  obtain ⟨W, hW, hinj, -⟩ := _root_.GlobalTheory.eulerOp_injective_eigen ι (fun v => Γ ⧸ K.comap (c v)) x0 H a' s B' Z h1 hs hs1 hfin
    hnorm hx0 hrec
  refine ⟨W, hinj, fun x y => ?_⟩
  have hW' := (Equiv.hasSum_iff e).mpr hW
  have hfun : ((fun f : {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ x0 w}.Finite} =>
      (∏ᶠ v, a' v (f.1 v)) • B' f.1) ∘ e) = fun q => a q.out • B q.out := by
    funext q
    have hq : ∀ v, (e q).1 v = (QuotientGroup.mk q.out : Γ ⧸ K.comap (c v)) := by
      intro v
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      exact he _ v
    simp only [Function.comp]
    rw [B'eval _ q.out hq]
    congr 1
    rw [hfac q.out]
    exact finprod_congr fun v => by simp only [a']; rw [hq v]; exact acv v q.out
  rw [hfun] at hW'
  have := hW'.mapL ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y))
  simpa [inner_smul_right] using this

end GlobalTheory
end

