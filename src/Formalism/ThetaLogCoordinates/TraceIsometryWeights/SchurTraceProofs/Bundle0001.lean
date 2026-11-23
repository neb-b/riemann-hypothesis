module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds
section
namespace Formalism.InvariantFactorPaths.PW

open Finset

section gen

variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]

theorem homAct_apply (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (φ : V →ₗ[K] W) (x : V) :
    homAct EV EW a b φ x = EW a b (φ x) - φ (EV a b x) := rfl

theorem homAct_postcomp {W' : Type} [AddCommGroup W'] [Module K W'] (EV : ι → ι → Module.End K V)
    (EW : ι → ι → Module.End K W) (EW' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (hθ : ∀ a b x, θ (EW a b x) = EW' a b (θ x)) (a b : ι) (φ : V →ₗ[K] W) :
    θ ∘ₗ (homAct EV EW a b φ) = homAct EV EW' a b (θ ∘ₗ φ) := by
  ext x
  simp [homAct_apply, hθ]

theorem homAct_precomp {V' : Type} [AddCommGroup V'] [Module K V'] (EV : ι → ι → Module.End K V)
    (EV' : ι → ι → Module.End K V') (EW : ι → ι → Module.End K W) (ι' : V' →ₗ[K] V)
    (hι : ∀ a b x, ι' (EV' a b x) = EV a b (ι' x)) (a b : ι) (φ : V →ₗ[K] W) :
    (homAct EV EW a b φ) ∘ₗ ι' = homAct EV' EW a b (φ ∘ₗ ι') := by
  ext x
  simp [homAct_apply, hι]

def postC (X : Module.End K W) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => X ∘ₗ φ
  map_add' := by intro φ ψ; ext x; simp
  map_smul' := by intro c φ; ext x; simp

def preC (Y : Module.End K V) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => φ ∘ₗ Y
  map_add' := by intro φ ψ; ext x; simp
  map_smul' := by intro c φ; ext x; simp

theorem postC_apply (X : Module.End K W) (φ : V →ₗ[K] W) (x : V) : postC X φ x = X (φ x) := rfl

theorem preC_apply (Y : Module.End K V) (φ : V →ₗ[K] W) (x : V) : preC (W := W) Y φ x = φ (Y x) := rfl

theorem postC_pow_apply (X : Module.End K W) (i : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((postC X) ^ i) φ x = (X ^ i) (φ x) := by
  induction i generalizing φ with
  | zero => simp
  | succ i ih =>
    rw [pow_succ (postC (V := V) X) i, pow_succ X i]
    exact ih (postC X φ)

theorem preC_pow_apply (Y : Module.End K V) (j : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((preC (W := W) Y) ^ j) φ x = φ ((Y ^ j) x) := by
  induction j generalizing φ with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (preC (W := W) Y) j, pow_succ' Y j]
    exact ih (preC Y φ)

theorem postC_preC_commute (X : Module.End K W) (Y : Module.End K V) :
    Commute (postC (V := V) X) (preC (W := W) Y) := by
  show postC (V := V) X * preC (W := W) Y = preC (W := W) Y * postC (V := V) X
  ext φ x
  rfl

theorem homAct_eq (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) :
    homAct EV EW a b = postC (EW a b) + -preC (EV a b) := by
  ext φ x
  simp only [homAct_apply, LinearMap.add_apply, LinearMap.neg_apply, postC_apply, preC_apply, sub_eq_add_neg]

theorem homAct_pow_apply (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (k : ℕ)
    (φ : V →ₗ[K] W) (x : V) :
    ((homAct EV EW a b) ^ k) φ x =
      ∑ m ∈ antidiagonal k, ((k.choose m.1 : K) * (-1) ^ m.2) • ((EW a b) ^ m.1) (φ (((EV a b) ^ m.2) x)) := by
  have hc : Commute (postC (V := V) (EW a b)) ((-1 : K) • preC (W := W) (EV a b)) :=
    (postC_preC_commute (EW a b) (EV a b)).smul_right (-1 : K)
  have he : homAct EV EW a b = postC (EW a b) + (-1 : K) • preC (EV a b) := by
    rw [homAct_eq, neg_one_smul]
  rw [he, hc.add_pow', LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_pow, mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, postC_pow_apply, preC_pow_apply]

end gen

theorem hom_relation_holds : HomRel := by
  intro K V W ι _ _ _ _ _ _ EV EW hV hW
  unfold GlRel at *
  intro a b c d
  ext φ x
  have h1 := LinearMap.congr_fun (hW a b c d) (φ x)
  have h2 := congrArg φ (LinearMap.congr_fun (hV a b c d) x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, homAct_apply, map_sub] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;>
    simp only [LinearMap.zero_apply, map_zero, homAct_apply, sub_zero, zero_sub, map_neg, LinearMap.sub_apply, map_sub] at h1 h2 ⊢ <;>
    rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2] <;> abel

theorem hom_divided_holds : HomDiv := by
  intro p _ V W ι _ _ _ _ _ EV EW L M hM hL hW
  unfold ZpClosed DivStable HomLat at *
  refine ⟨fun c hc φ hφ => ?_, fun a b hab k φ hφ => ?_⟩
  · have hφ' : ∀ y ∈ L, φ y ∈ M := hφ
    show ∀ y ∈ L, (c • φ) y ∈ M
    intro y hy
    exact hM c hc _ (hφ' y hy)
  · have hφ' : ∀ y ∈ L, φ y ∈ M := hφ
    show ∀ y ∈ L, ((k.factorial : Padic p)⁻¹ • (homAct EV EW a b ^ k) φ) y ∈ M
    intro x hx
    rw [LinearMap.smul_apply, homAct_pow_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem M fun m hm => ?_
    have hm' : m.1 + m.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
    have hx2 := hL a b hab m.2 x hx
    have hy := hW a b hab m.1 _ (hφ' _ hx2)
    have hn : ‖((-1 : Padic p) ^ m.2)‖ ≤ 1 := by simp
    have hz := hM _ hn _ hy
    simp only [map_smul, smul_smul] at hz
    simp only [smul_smul]
    convert hz using 2
    subst hm'
    have h1 : (m.1.factorial : Padic p) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (m.2.factorial : Padic p) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcn := Nat.add_choose_mul_factorial_mul_factorial m.2 m.1
    rw [add_comm m.2 m.1] at hcn
    have hc : ((m.1 + m.2).choose m.1 : Padic p) * m.2.factorial * m.1.factorial = (m.1 + m.2).factorial := by
      exact_mod_cast hcn
    rw [← hc]
    have h3 : ((m.1 + m.2).choose m.1 : Padic p) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right m.1 m.2)).ne'
    field_simp

theorem hom_trace_holds : HomTrace := by
  intro K V ι _ _ _ _ _ EV ψ hψ
  have h : (⨆ a, ⨆ b, ⨆ (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) ≤
      LinearMap.ker (LinearMap.trace K V) := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_
    rintro _ ⟨φ, rfl⟩
    rw [LinearMap.mem_ker]
    show LinearMap.trace K V (EV a b * φ - φ * EV a b) = 0
    rw [map_sub, LinearMap.trace_mul_comm, sub_self]
  exact LinearMap.mem_ker.mp (h hψ)

end Formalism.InvariantFactorPaths.PW
end

-- bundled from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInt
section
namespace Formalism.InvariantFactorPaths.PW

open Finset

section gen

variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]

def lop (A B : Module.End K W) : Module.End K (Module.End K W) :=
  LinearMap.mulLeft K A * LinearMap.mulRight K B

theorem lop_apply (A B X : Module.End K W) : lop A B X = A * X * B := by
  simp [lop, mul_assoc]

theorem lop_pow_apply (A B X : Module.End K W) (k : ℕ) : (lop A B ^ k) X = A ^ k * X * B ^ k := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, lop_apply, pow_succ A k, pow_succ' B k]
    simp only [mul_assoc]

theorem lop_commute {A B A' B' : Module.End K W} (hA : Commute A A') (hB : Commute B B') :
    Commute (lop A B) (lop A' B') := by
  show lop A B * lop A' B' = lop A' B' * lop A B
  refine LinearMap.ext fun X => ?_
  simp only [Module.End.mul_apply, lop_apply]
  have e1 : A * (A' * X * B') * B = (A * A') * X * (B' * B) := by simp only [mul_assoc]
  have e2 : A' * (A * X * B) * B' = (A' * A) * X * (B * B') := by simp only [mul_assoc]
  rw [e1, e2, hA.eq, hB.eq]

theorem Om_eq_pow (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) (q : ℕ) :
    Om E S z q = ((∑ i ∈ S, lop (E z i) (E i z)) ^ q) 1 := by
  induction q with
  | zero => simp [Om]
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih, LinearMap.sum_apply]
    simp only [lop_apply]
    rfl

theorem GlRel.commF {E : ι → ι → Module.End K W} (h : GlRel E) {z i j : ι} (hi : i ≠ z) (hj : j ≠ z) :
    Commute (E z i) (E z j) := by
  have := h z i z j
  simp only [hi, hj, if_false, sub_self] at this
  exact sub_eq_zero.mp this

theorem GlRel.commE {E : ι → ι → Module.End K W} (h : GlRel E) {z i j : ι} (hi : i ≠ z) (hj : j ≠ z) :
    Commute (E i z) (E j z) := by
  have := h i z j z
  simp only [Ne.symm hi, Ne.symm hj, if_false, sub_self] at this
  exact sub_eq_zero.mp this

theorem Om_insert {E : ι → ι → Module.End K W} (h : GlRel E) {S : Finset ι} {z i : ι} (hz : z ∉ insert i S)
    (hi : i ∉ S) (q : ℕ) :
    Om E (insert i S) z q =
      ∑ k ∈ range (q + 1), (q.choose k : K) • ((E z i) ^ k * Om E S z (q - k) * (E i z) ^ k) := by
  have hzi : i ≠ z := fun e => hz (e ▸ Finset.mem_insert_self _ _)
  have hcomm : Commute (lop (E z i) (E i z)) (∑ j ∈ S, lop (E z j) (E j z)) := by
    refine Commute.sum_right _ _ _ fun j hj => ?_
    have hjz : j ≠ z := fun e => hz (e ▸ Finset.mem_insert_of_mem hj)
    exact lop_commute (h.commF hzi hjz) (h.commE hzi hjz)
  rw [Om_eq_pow, Finset.sum_insert hi, hcomm.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    ← Om_eq_pow, lop_pow_apply, ← Nat.cast_smul_eq_nsmul K]

end gen

section padic

variable {p : ℕ} [Fact p.Prime]

theorem norm_pow_p_le_one (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

theorem norm_pow_log_div_choose {n k N : ℕ} (hk : k ≤ n) (hn : n ≤ N) :
    ‖(p : ℚ_[p]) ^ (Nat.log p N) / (n.choose k : ℚ_[p])‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hv : (n.choose k).factorization p ≤ Nat.log p N :=
    Nat.factorization_choose_le_log.trans (Nat.log_mono_right hn)
  have hdecomp : ((n.choose k : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ ((n.choose k).factorization p) *
      ((n.choose k / p ^ ((n.choose k).factorization p) : ℕ) : ℚ_[p]) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hr : ‖((n.choose k / p ^ ((n.choose k).factorization p) : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_ordCompl hp hC))
  rw [hdecomp, norm_div, norm_mul, hr, mul_one, Padic.norm_p_pow, Padic.norm_p_pow,
    div_le_one (zpow_pos (by exact_mod_cast hp.pos) _)]
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp.one_lt.le) (by omega)

variable {W ι : Type} [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]

theorem Om_int {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) (z : ι) (N : ℕ) (S : Finset ι) : z ∉ S → ∀ c q : ℕ, q + c ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (S.card * Nat.log p N) *
        ((c.factorial : ℚ_[p]) / (((q + c).factorial : ℚ_[p]) * (q.factorial : ℚ_[p])))) • Om E S z q u ∈ M := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ c q _ u hu
    cases q with
    | zero => simpa [Om, Nat.factorial_ne_zero] using hu
    | succ q => simpa [Om] using M.zero_mem
  | insert i S hi ih =>
    intro hz c q hqc u hu
    have hzi : z ≠ i := fun e => hz (e ▸ Finset.mem_insert_self _ _)
    have hzS : z ∉ S := fun e => hz (Finset.mem_insert_of_mem e)
    rw [Om_insert hE hz hi q, LinearMap.sum_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun k hk => ?_
    have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hu' : ((k.factorial : ℚ_[p]))⁻¹ • ((E i z) ^ k) u ∈ M := hD i z (Ne.symm hzi) k u hu
    have hY := ih hzS (c + k) (q - k) (by omega) _ hu'
    have hDY := hD z i hzi k _ hY
    have hnorm := norm_pow_log_div_choose (p := p) (n := c + k) (k := k) (N := N) (by omega)
      (by omega)
    have key := hZ _ hnorm _ hDY
    convert key using 1
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    congr 1
    have hqk : q - k + (c + k) = q + c := by omega
    rw [hqk, Finset.card_insert_of_notMem hi, Nat.cast_choose ℚ_[p] hkq,
      Nat.cast_choose ℚ_[p] (Nat.le_add_left k c), Nat.add_sub_cancel]
    have h1 : (c.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : ((q - k).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : ((q + c).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h5 : (q.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h6 : ((c + k).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring

theorem Pstep_int {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) {z : ι} {S : Finset ι} (hz : z ∉ S) (l : ℕ) {u : W} (hu : u ∈ M) :
    ((p : ℚ_[p]) ^ (S.card * Nat.log p (l + S.card))) • Pstep E S z l u ∈ M := by
  unfold Pstep
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun q hq => ?_
  have hql : q ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have h := Om_int hE hZ hD z (l + S.card) S hz S.card q (by omega) u hu
  have h2 := hZ ((-1 : ℚ_[p]) ^ q) (by simp) _ h
  convert h2 using 1
  simp only [LinearMap.smul_apply, smul_smul]
  congr 1
  ring

end padic

theorem invariant_integral_holds : InvInt := by
  intro p _ W ι _ _ _ E hE M hZ hD l L hL u hu
  have up : ∀ (a b : ℕ) (x : W), a ≤ b → (p : ℚ_[p]) ^ a • x ∈ M → (p : ℚ_[p]) ^ b • x ∈ M := by
    intro a b x hab hx
    have := hZ _ (norm_pow_p_le_one (p := p) (b - a)) _ hx
    rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hab] at this
  have main : ∀ (L : List ι), L.Nodup → ∀ N, l + L.length - 1 ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (L.length.choose 2 * Nat.log p N)) • InvOp E l L u ∈ M := by
    intro L
    induction L with
    | nil =>
      intro _ N _ u hu
      simpa [InvOp] using hu
    | cons z L ih =>
      intro hnd N hN u hu
      rw [List.nodup_cons] at hnd
      obtain ⟨hzL, hnd⟩ := hnd
      simp only [List.length_cons] at hN
      have hv := ih hnd N (by omega) u hu
      have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
      have hz : z ∉ L.toFinset := by simpa using hzL
      have hP := Pstep_int hE hZ hD hz l hv
      rw [hcard] at hP
      have hP' := up _ (L.length * Nat.log p N) _
        (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))) hP
      convert hP' using 1
      rw [InvOp, Module.End.mul_apply, map_smul, smul_smul, ← pow_add, List.length_cons,
        Nat.choose_succ_succ, Nat.choose_one_right]
      congr 2
      ring
  exact main L hL (l + L.length - 1) le_rfl u hu

end Formalism.InvariantFactorPaths.PW
end

