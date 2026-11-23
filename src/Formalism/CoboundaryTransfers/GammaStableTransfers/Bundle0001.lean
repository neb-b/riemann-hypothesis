module

public import Formalism.CoboundaryTransfers.StatementAPI

@[expose] public section

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.DiffOneSmulOfTower
section
noncomputable section

namespace Formalism.CoboundaryTransfers

section DiagramChase₂
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

lemma chase_qpow_bij (W : WachMod B M D) (j : ℕ) :
    Function.Bijective (fun x : D => B.Q ^ j • x) := by
  induction j with
  | zero =>
    simp only [pow_zero, one_smul]
    exact Function.bijective_id
  | succ n ih =>
    have h : (fun x : D => B.Q ^ (n + 1) • x) = (fun x : D => B.Q ^ n • x) ∘ (fun x : D => B.Q • x) := by
      funext x
      simp only [Function.comp, pow_succ, mul_smul]
    rw [h]
    exact ih.comp W.Q_bij

lemma chase_Q_sub (W : WachMod B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) :
    W.QInv (x - y) := by
  show B.Q ^ M • (x - y) ∈ W.N
  rw [smul_sub]
  exact W.N.sub_mem hx hy
lemma chase_Q_smul (W : WachMod B M D) (r : O) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by
  show B.Q ^ M • (r • x) ∈ W.N
  rw [algebra_compatible_smul A r x, smul_comm (B.Q ^ M) (algebraMap O A r) x]
  exact W.N.smul_mem _ hx
lemma chase_Q_smulA (W : WachMod B M D) (b : A) {x : D} (hx : W.QInv x) : W.QInv (b • x) := by
  show B.Q ^ M • (b • x) ∈ W.N
  rw [smul_comm (B.Q ^ M) b x]
  exact W.N.smul_mem b hx
lemma chase_Q_N (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := by
  show B.Q ^ M • x ∈ W.N
  exact W.N.smul_mem _ hx
lemma chase_Q_φ (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x) := by
  show B.Q ^ M • W.φ x ∈ W.N
  exact W.φ_N x hx

lemma WachMod_d1_smul (W : WachMod B M D) (r : O) (y z : D) :
    W.d1 (r • y) (r • z) = r • W.d1 y z := by
  simp only [WachMod.d1, map_smul, smul_sub]
lemma diffOne_sub (W : WachMod B M D) (y z y' z' : D) :
    W.d1 (y - y') (z - z') = W.d1 y z - W.d1 y' z' := by
  simp only [WachMod.d1, map_sub]
  abel
lemma WachMod_d1_phi_sub_gamma_sub_eq_zero (W : WachMod B M D) (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  have hc : ∀ y : D, W.φ (W.γ y) = W.γ (W.φ y) := by
    cases W
    assumption
  simp only [WachMod.d1, map_sub, hc]
  abel
lemma map_diffOne {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') (y z : D) :
    f.f (W.d1 y z) = W'.d1 (f.f y) (f.f z) := by
  have hφ : ∀ x, f.f (W.φ x) = W'.φ (f.f x) := by
    cases f
    first | assumption | done
  have hγ : ∀ x, f.f (W.γ x) = W'.γ (f.f x) := by
    cases f
    first | assumption | done
  simp only [WachMod.d1, map_sub, hφ, hγ]
lemma chase_hom_Q {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') {y : D}
    (hy : W.QInv y) : W'.QInv (f.f y) := by
  have hN : ∀ x ∈ W.N, f.f x ∈ W'.N := by
    cases f
    first | assumption | done
  show B.Q ^ M • f.f y ∈ W'.N
  rw [← map_smul f.f]
  exact hN _ hy

end DiagramChase₂

private lemma exists_phi_X_eq_X_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) :
    ∃ v, B.φ B.X = B.X * v := by
  cases B
  assumption

theorem cocycleLiftOfExact_holds : DiagramChase₂ := by
  unfold DiagramChase₂
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hC hR hT
  unfold CokerKilled at hC
  unfold RatSurj at hR
  unfold WachMod.TorsKilled at hT
  unfold Lifts

  have hpφ : ∀ t, S.π.f (W₁.φ t) = W₂.φ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hpγ : ∀ t, S.π.f (W₁.γ t) = W₂.γ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hiN : ∀ t ∈ W₀.N, S.ι.f t ∈ W₁.N := by
    generalize S.ι = g
    cases g
    assumption
  have hpO : ∀ (r : O) (t : D₁), S.π.f (r • t) = r • S.π.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]
  have hiO : ∀ (r : O) (t : D₀), S.ι.f (r • t) = r • S.ι.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]

  have key : ∀ (w : D₀) (t : D₁), S.ι.f w = B.X • t → ∃ t₀, S.ι.f t₀ = t ∧ w = B.X • t₀ := by
    intro w t h
    have h0 : S.π.f t = 0 := by
      apply W₂.X_inj
      rw [← map_smul, ← h]
      exact (S.exact _).2 ⟨w, rfl⟩
    obtain ⟨t₀, ht₀⟩ := (S.exact t).1 h0
    refine ⟨t₀, ht₀, S.ι_inj ?_⟩
    rw [map_smul, ht₀, h]
  have qsat : ∀ w : D₀, W₁.QInv (S.ι.f w) → W₀.QInv w := by
    intro w h
    show B.Q ^ M • w ∈ W₀.N
    apply S.sat
    rw [map_smul]
    exact h
  intro y z hyz
  obtain ⟨k, y₁, z₁, hc₁, x, hx, hpy₁, hpz₁⟩ := hR y z hyz
  obtain ⟨⟨hQy, n, hn, rfl⟩, hd⟩ := hyz
  obtain ⟨⟨hQy₁, n₁, hn₁, hz₁⟩, hd₁⟩ := hc₁

  obtain ⟨a, ha, hpa⟩ := hC (B.Q ^ M • y) hQy
  obtain ⟨yt, hyt⟩ : ∃ t, B.Q ^ M • t = a := (chase_qpow_bij W₁ M).2 a
  have hQyt : W₁.QInv yt := by
    show B.Q ^ M • yt ∈ W₁.N
    rw [hyt]
    exact ha
  have hpyt : S.π.f yt = ((B.p : O) ^ e) • y := by
    apply (chase_qpow_bij W₂ M).1
    show B.Q ^ M • S.π.f yt = B.Q ^ M • (((B.p : O) ^ e) • y)
    rw [← map_smul S.π.f, hyt, hpa, smul_comm (B.Q ^ M) ((B.p : O) ^ e) y]
  obtain ⟨b, hb, hpb⟩ := hC n hn
  have hpzt : S.π.f (B.X • b) = ((B.p : O) ^ e) • (B.X • n) := by
    rw [map_smul, hpb, smul_comm B.X ((B.p : O) ^ e) n]
  have hω₁ : S.π.f (W₁.d1 yt (B.X • b)) = 0 := by
    rw [map_diffOne, hpyt, hpzt, WachMod_d1_smul, hd, smul_zero]
  obtain ⟨ω, hω⟩ := (S.exact _).1 hω₁

  obtain ⟨y', hQy', hγyt⟩ := W₁.γ_QN yt hQyt
  obtain ⟨v, hv⟩ := exists_phi_X_eq_X_mul B
  have hiω : S.ι.f ω = B.X • (y' - (v • W₁.φ b - b)) := by
    rw [hω, WachMod.d1, hγyt, W₁.φ_smul, hv, mul_smul, smul_sub, smul_sub]
  have hsmem : W₁.QInv (y' - (v • W₁.φ b - b)) :=
    chase_Q_sub W₁ hQy' (chase_Q_sub W₁ (chase_Q_smulA W₁ v (chase_Q_φ W₁ hb)) (chase_Q_N W₁ hb))
  obtain ⟨s₀, hs₀, hωs₀⟩ := key ω _ hiω
  have hC2 : W₀.C2 ω := ⟨s₀, qsat s₀ (by rw [hs₀]; exact hsmem), hωs₀⟩

  obtain ⟨m, hm, hpm⟩ := hC x hx
  have hpu : S.π.f (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • y) := by
    rw [map_sub, map_sub, hpO, hpφ, hpy₁, hpm, map_smul W₂.φ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) y]
    abel
  have hpv : S.π.f (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • (B.X • n)) := by
    rw [map_sub, map_sub, hpO, hpγ, hpz₁, hpm, map_smul W₂.γ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) (B.X • n)]
    abel
  have hα0 : S.π.f (((B.p : O) ^ k) • yt - (((B.p : O) ^ e) • y₁ - (W₁.φ m - m))) = 0 := by
    rw [map_sub, hpO, hpyt, hpu, sub_self]
  have hβ0 : S.π.f (((B.p : O) ^ k) • (B.X • b) - (((B.p : O) ^ e) • z₁ - (W₁.γ m - m))) = 0 := by
    rw [map_sub, hpO, hpzt, hpv, sub_self]
  obtain ⟨α, hα⟩ := (S.exact _).1 hα0
  obtain ⟨β, hβ⟩ := (S.exact _).1 hβ0
  have hduv : W₁.d1 (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = 0 := by
    rw [diffOne_sub, WachMod_d1_smul, hd₁, smul_zero, WachMod_d1_phi_sub_gamma_sub_eq_zero, sub_zero]
  have hdαβ : W₀.d1 α β = ((B.p : O) ^ k) • ω := by
    apply S.ι_inj
    rw [map_diffOne, hα, hβ, diffOne_sub, hduv, sub_zero, WachMod_d1_smul, ← hω, hiO]
  have hQu : W₁.QInv (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) :=
    chase_Q_sub W₁ (chase_Q_smul W₁ _ hQy₁) (chase_Q_sub W₁ (chase_Q_φ W₁ hm) (chase_Q_N W₁ hm))
  have hQα : W₀.QInv α := qsat α (by rw [hα]; exact chase_Q_sub W₁ (chase_Q_smul W₁ _ hQyt) hQu)
  obtain ⟨m', hm', hγm⟩ := W₁.γ_N m hm
  have hiβ : S.ι.f β = B.X • (((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m')) := by
    rw [hβ, hz₁, hγm, smul_sub, smul_sub, smul_comm B.X ((B.p : O) ^ k) b, smul_comm B.X ((B.p : O) ^ e) n₁]
  have hKb : ((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m') ∈ W₁.N :=
    W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hb) (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁) hm')
  obtain ⟨β₀, hβ₀, hββ₀⟩ := key β _ hiβ
  have hcob : W₀.IsCob2 (((B.p : O) ^ k) • ω) :=
    ⟨α, β, ⟨hQα, β₀, S.sat β₀ (by rw [hβ₀]; exact hKb), hββ₀⟩, hdαβ.symm⟩

  obtain ⟨α', β', ⟨hQα', n', hn', hβ'⟩, hcω⟩ := hT ω hC2 ⟨k, hcob⟩
  refine ⟨c • yt - S.ι.f α', c • (B.X • b) - S.ι.f β', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact chase_Q_sub W₁ (chase_Q_smul W₁ c hQyt) (chase_hom_Q S.ι hQα')
  · refine ⟨c • b - S.ι.f n', W₁.N.sub_mem (W₁.N.smul_of_tower_mem c hb) (hiN n' hn'), ?_⟩
    rw [hβ', map_smul, smul_sub, smul_comm B.X c b]
  · rw [diffOne_sub, WachMod_d1_smul, ← map_diffOne S.ι α' β', ← hcω, ← hω, hiO, sub_self]
  · rw [map_sub, hpO, hpyt, (S.exact _).2 ⟨α', rfl⟩, sub_zero, mul_comm, mul_smul]
  · rw [map_sub, hpO, hpzt, (S.exact _).2 ⟨β', rfl⟩, sub_zero, mul_comm, mul_smul]

end Formalism.CoboundaryTransfers
end
end

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
section
noncomputable section

namespace Formalism.CoboundaryTransfers

namespace WachMod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]

theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx

theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy

theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy

theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩

theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz

theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩

theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]

theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩

end WachMod

end Formalism.CoboundaryTransfers
end
end

-- bundled from Formalism.CoboundaryTransfers.GammaStableTransfers.TorsionKilledCriterionHolds
section
noncomputable section

namespace Formalism.CoboundaryTransfers

theorem gammaGradedStep_holds : GradedStep := by
  intro O A _ _ _ B M D _ _ _ _ W u hu i n hn
  obtain ⟨t, ht⟩ := hu
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap O A u + B.X * t) ^ k
      = algebraMap O A (u ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap O A u + B.X * t) + algebraMap O A (u ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap O A u + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A (u ^ i) (B.X ^ i • n)]
    module

theorem gammaImageProduct_holds : GammaOnto := by
  intro O A _ _ _ B M D _ _ _ _ W u a hyp
  suffices h : ∀ j, j ≤ a → ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 j, (1 - u ^ i)) • (B.X • n) =
        (W.γ (B.X • x) - B.X • x) + B.X ^ (j + 1) • z' from h a le_rfl
  intro j
  induction j with
  | zero => intro _ n hn; exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ j ih =>
    intro hj n hn
    obtain ⟨x, hx, m, hm, he⟩ := ih (by omega) n hn
    obtain ⟨n', hn', hg⟩ := hyp (j+1) (by omega) hj m hm
    refine ⟨(1 - u^(j+1)) • x - B.X ^ j • m, ?_, n', hn', ?_⟩
    · exact W.N.sub_mem (W.N.smul_of_tower_mem _ hx) (W.N.smul_mem _ hm)
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • ((1 - u^(j+1)) • x - B.X ^ j • m)
          = (1 - u^(j+1)) • (B.X • x) - B.X ^ (j+1) • m := by
        rw [smul_sub, smul_comm, smul_smul, ← pow_succ']
      rw [e1, map_sub, LinearMap.map_smul, hg]
      simp only [smul_sub, smul_add, sub_smul, one_smul]
      abel

section Claim
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

lemma aeval_stable (δ : D →ₗ[O] D) (S : Submodule O D) (hS : ∀ y ∈ S, δ y ∈ S)
    (f : Polynomial O) : ∀ y ∈ S, Polynomial.aeval δ f y ∈ S := by
  induction f using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact S.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add (f := _), LinearMap.add_apply]
    exact S.add_mem (hp y hy) (hq y hy)
  | monomial n a ih =>
    intro y hy
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS y hy)

def QS (W : WachMod B M D) : Submodule O D where
  carrier := {y | B.Q ^ M • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.Q ^ M • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.Q ^ M • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.Q ^ M • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy

lemma N_QInv (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := W.N.smul_mem _ hx

lemma QInv_smulA (W : WachMod B M D) (b : A) {y : D} (hy : W.QInv y) : W.QInv (b • y) := by
  show B.Q ^ M • (b • y) ∈ W.N
  rw [smul_comm]
  exact W.N.smul_mem b hy

lemma δ_QInv (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ y, W.QInv y → W.QInv (δ y) := by
  intro y hy
  obtain ⟨y', hy', hyy⟩ := W.γ_QN y hy
  have h3 : δ y = y' := by
    have h := W.X_inj (δ y - y') (by rw [smul_sub, h2, hyy, sub_self])
    exact sub_eq_zero.mp h
  show B.Q ^ M • δ y ∈ W.N
  rw [h3]
  exact hy'

lemma δ_N (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ n ∈ W.N, δ n ∈ W.N := by
  intro n hn
  obtain ⟨x', hx', hxx⟩ := W.γ_N n hn
  have h3 : δ n = x' := by
    have h := W.X_inj (δ n - x') (by rw [smul_sub, h2, hxx, sub_self])
    exact sub_eq_zero.mp h
  rw [h3]
  exact hx'

lemma claim_key (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (w : D) (hw : W.QInv w) (j : ℕ) (y z : D) (hyz : W.C1 y z)
    (hj : ((B.p : O) ^ j) • (B.X • w) = W.d1 y z) :
    Polynomial.aeval δ R (cΓ • w) ∈ W.N := by
  have δN := δ_N W δ h2
  have RN : ∀ f : Polynomial O, ∀ n ∈ W.N, Polynomial.aeval δ f n ∈ W.N :=
    fun f => aeval_stable δ (W.N.restrictScalars O) δN f
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  have Lφ : ∀ m ∈ W.N, ∃ m' ∈ W.N, W.φ (B.X ^ (a + 1) • m) = B.X ^ (a + 1) • m' := by
    intro m hm
    obtain ⟨v, hv⟩ := h1
    refine ⟨v ^ (a + 1) • B.Q ^ (k * (a + 1) - M) • (B.Q ^ M • W.φ m),
      W.N.smul_mem _ (W.N.smul_mem _ (W.φ_N m hm)), ?_⟩
    have hexp : B.Q ^ (k * (a + 1) - M) * B.Q ^ M = (B.Q ^ k) ^ (a + 1) := by
      rw [← pow_add, Nat.sub_add_cancel h1', pow_mul]
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc (B.X ^ (a + 1) * v ^ (a + 1)), hexp]
    ring
  have φπ : ∀ x ∈ W.N, W.QInv (W.φ (B.X • x)) := by
    intro x hx
    rw [W.φ_smul]; exact QInv_smulA W _ (W.φ_N x hx)
  have tf : ∀ i : ℕ, ∀ v, W.QInv v → ((B.p : O) ^ i) • v ∈ W.N → v ∈ W.N := by
    intro i
    induction i with
    | zero => intro v _ h; simpa using h
    | succ i ih =>
      intro v hv h
      apply ih v hv
      apply h4 _ ((QS W).smul_mem _ hv)
      rw [smul_smul, ← pow_succ']; exact h
  obtain ⟨hy, n, hn, hzn⟩ := hyz
  subst hzn
  obtain ⟨x, hx, z', hz', hc⟩ := h6 n hn
  obtain ⟨m', hm', hφm⟩ := Lφ z' hz'
  set Y' := cΓ • y - (W.φ (B.X • x) - B.X • x) with hY'
  have hY'Q : W.QInv Y' :=
    (QS W).sub_mem ((QS W).smul_mem _ hy) ((QS W).sub_mem (φπ x hx) (N_QInv W (W.N.smul_mem _ hx)))
  have eA : B.X • (cΓ • ((B.p : O) ^ j) • w - δ Y' - B.X ^ a • (z' - m')) = 0 := by
    have e1 : cΓ • ((B.p : O) ^ j) • (B.X • w) = cΓ • W.d1 y (B.X • n) := by rw [hj]
    have e2 : cΓ • W.d1 y (B.X • n) = (W.γ Y' - Y') + (B.X ^ (a + 1) • z' - B.X ^ (a + 1) • m') := by
      simp only [WachMod.d1, smul_sub, ← LinearMap.map_smul, hc, hY', map_sub, map_add (f := _), W.comm, hφm]
      abel
    rw [smul_sub, smul_sub, h2, smul_comm B.X cΓ, smul_comm B.X ((B.p : O) ^ j), e1, e2,
      smul_smul, ← pow_succ', smul_sub]
    abel
  have eA' : cΓ • ((B.p : O) ^ j) • w = δ Y' + B.X ^ a • (z' - m') := by
    have := W.X_inj _ eA; rw [sub_sub, sub_eq_zero] at this; exact this
  have eB : ((B.p : O) ^ j) • (cΓ • Polynomial.aeval δ R w) ∈ W.N := by
    rw [smul_comm, ← LinearMap.map_smul, ← LinearMap.map_smul, eA', map_add (f := _)]
    refine W.N.add_mem ?_ (RN R _ (W.N.smul_mem _ (W.N.sub_mem hz' hm')))
    have : Polynomial.aeval δ R (δ Y') = Polynomial.aeval δ (Polynomial.X * R) Y' := by
      rw [mul_comm, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [this]; exact h3 Y' hY'Q
  rw [LinearMap.map_smul]
  exact tf j _ ((QS W).smul_mem _ (RQ R w hw)) eB

lemma claim_fin (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a : ℕ) (cΓ : O)
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (h7 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z))
    (w : D) (hw : W.QInv w) (hm : Polynomial.aeval δ R w ∈ W.N) :
    W.IsCob2 ((R.eval 0 * cΓ) • (B.X • w)) := by
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  obtain ⟨R1, hR1⟩ := Polynomial.X_dvd_sub_C (p := R)
  have eD : (R.eval 0) • w = Polynomial.aeval δ R w - δ (Polynomial.aeval δ R1 w) := by
    have : R = Polynomial.C (R.coeff 0) + Polynomial.X * R1 := by rw [← hR1]; ring
    conv_rhs => rw [this]
    rw [map_add (f := _), map_mul, Polynomial.aeval_C, Polynomial.aeval_X, LinearMap.add_apply,
      Module.End.mul_apply, Polynomial.coeff_zero_eq_eval_zero, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Module.End.one_apply]
    abel
  obtain ⟨x2, hx2, z2, hz2, hc2⟩ := h6 _ hm
  obtain ⟨z3, hz3, h73⟩ := h7 z2 hz2
  refine ⟨B.X • x2 - cΓ • Polynomial.aeval δ R1 w, B.X • (B.X ^ a • z3),
    ⟨?_, _, W.N.smul_mem _ hz3, rfl⟩, ?_⟩
  · exact (QS W).sub_mem (N_QInv W (W.N.smul_mem _ hx2)) ((QS W).smul_mem _ (RQ R1 w hw))
  · have e3 : B.X • (B.X ^ a • z3) = B.X ^ (a + 1) • z3 := by rw [smul_smul, ← pow_succ']
    simp only [WachMod.d1, e3]
    have e4 : (R.eval 0 * cΓ) • (B.X • w) = cΓ • (B.X • ((R.eval 0) • w)) := by
      rw [mul_comm, mul_smul, smul_comm (R.eval 0) B.X]
    rw [e4, eD, smul_sub, smul_sub, hc2, h73]
    simp only [h2, map_sub, LinearMap.map_smul, smul_sub]
    abel

theorem torsionKilledCriterion_holds : CoboundaryTransfer := by
  intro O A _ _ _ B M D _ _ _ _ W δ R a k cΓ h1 h1' h2 h3 h4 h5 h6 h7
    ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩
  subst hωw
  have hk := claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj
  rw [LinearMap.map_smul] at hk
  have RQ : W.QInv (Polynomial.aeval δ R w) :=
    aeval_stable δ (QS W) (δ_QInv W δ h2) R w hw
  exact claim_fin W δ R a cΓ h2 h6 h7 w hw (h5 _ RQ hk)

end Claim

end Formalism.CoboundaryTransfers
end
end

