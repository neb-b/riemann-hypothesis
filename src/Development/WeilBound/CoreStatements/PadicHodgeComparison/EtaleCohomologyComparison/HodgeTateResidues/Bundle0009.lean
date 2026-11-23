module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.OneTmul
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.TfBaseField
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.DiffMem
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers TensorProduct

namespace CrystallineSemistableComparison.HT

open Pb

namespace CoB

theorem sub_H {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (h : ∀ T, Subsingleton (F.obj T)) (j : ℕ) : Subsingleton (CH.H F j) := by
  have : Subsingleton (CH.Cn F j) := ⟨fun _ _ => funext fun _ => (h _).elim _ _⟩
  exact Submodule.Quotient.mk_surjective _ |>.subsingleton

theorem hq_zero {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (ρ ρ' : ℤ) (h : ρ' ≤ 0) (j : ℕ) : Subsingleton (HQ Q ρ ρ' j) := by
  refine sub_H _ (fun T => ⟨fun x y => ?_⟩) j
  obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
  refine (sq_eq _ _ _ _).2 ?_
  change _ ∈ T.obj.pdPow ρ'.toNat
  rw [Int.toNat_eq_zero.2 h, T.obj.pdPow_zero]; trivial

variable {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K))

theorem mu_zero (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I)))) {t : B} (ht : t ∈ I) {a r : ℕ} (h : r < a) (j : ℕ)
    (y : Hdg q a j) : muG γ q Q ht a r j y = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))).trans (Submodule.Quotient.mk_zero _)
  obtain ⟨x, hx, e⟩ := sq_surj _ _ (z.1 (s ⋙ (kS γ q Q).G))
  refine Subtype.ext ?_
  change (kS γ q Q).qC (t ^ (r - a)) (b := thFil _ ((a : ℤ) + 1)) (b' := sFil Q ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B I γ 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx) _
    (show sqM _ _ _ from z.1 (s ⋙ (kS γ q Q).G)).1 = 0
  rw [← e]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (fil_mul_le (b := nlBase B I γ 0) ht (r := a) (r' := r + 1) (by omega) _ hx)

theorem diff_mem {B T : Type} [CommRing B] [CommRing T] {I : Ideal B} {γ : DividedPowers I} {J : Ideal T} (δ : DividedPowers J)
    (i : B →+* T) (hi : IsDPMorphism γ δ i) {a r : ℕ} (har : a ≤ r) {c b t : B} (hc : c - b * t ^ (r - a) ∈ pdP γ (r - a + 1))
    (x : T) (hx : x ∈ pdP δ a) : i c * x - i b * (i (t ^ (r - a)) * x) ∈ pdP δ (r + 1) := by
  have h1 := dividedPowerFiltration_mul δ _ _ (dividedPowerFiltration_map hi _ hc) hx
  rw [show r - a + 1 + a = r + 1 by omega] at h1
  convert h1 using 1
  rw [map_sub, map_mul]; ring

theorem sqC_res (s : ℕ) {t : B} (ht : t ∈ I) {a r : ℕ} (har : a ≤ r) (j : ℕ) (c b : B) (hc : c - b * t ^ (r - a) ∈ pdP γ (r - a + 1))
    (ha : (smO γ q 1 s {⊤}).LeC c (sFil _ (a : ℤ)) (sFil _ (r : ℤ)))
    (hb : (smO γ q 1 s {⊤}).LeC c (sFil _ ((a : ℤ) + 1)) (sFil _ ((r : ℤ) + 1))) (y : Hdg q a j) :
    ((smO γ q 1 s {⊤}).sqC c ha hb).pull j (resH q (TO q 1 s {⊤}) a j y) = b • muG γ q (TS γ q 1 s {⊤}) ht a r j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (congrArg Submodule.Quotient.mk (Subtype.ext (funext fun σ => ?_))).trans (Submodule.Quotient.mk_smul _ _ _)
  obtain ⟨x, hx, e⟩ := sq_surj _ _ (z.1 (σ ⋙ (kS γ q (TS γ q 1 s {⊤})).G))
  refine Subtype.ext ?_
  change (smO γ q 1 s {⊤}).qC c hb _ (show sqM _ _ _ from z.1 (σ ⋙ (kS γ q (TS γ q 1 s {⊤})).G)).1 =
    b • (kS γ q (TS γ q 1 s {⊤})).qC (t ^ (r - a)) (b := thFil _ ((a : ℤ) + 1)) (b' := sFil _ ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B I γ 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx) _
    (show sqM _ _ _ from z.1 (σ ⋙ (kS γ q (TS γ q 1 s {⊤})).G)).1
  rw [← e]
  exact Ideal.Quotient.eq.2 (diff_mem (σ.obj (Fin.last j)).obj.δ (σ.obj (Fin.last j)).obj.i (σ.obj (Fin.last j)).obj.compat har hc x hx)

theorem e_ex (s : ℕ) {t : B} (ht : t ∈ I) {a r : ℕ} (har : a ≤ r) (has : a < s) (j : ℕ) (ρ ρ' : ℤ) (h : ρ = a) (h' : ρ' = (a : ℤ) + 1) :
    ∃ e : Hdg q a j ≃ₗ[K] HQ (TO q 1 s {⊤}) ρ ρ' j, ∀ (c b : B), c - b * t ^ (r - a) ∈ pdP γ (r - a + 1) →
      ∀ (ha : (smO γ q 1 s {⊤}).LeC c (sFil _ ρ) (sFil _ (r : ℤ))) (hb : (smO γ q 1 s {⊤}).LeC c (sFil _ ρ') (sFil _ ((r : ℤ) + 1)))
        (y : Hdg q a j), ((smO γ q 1 s {⊤}).sqC c ha hb).pull j (e y) = b • muG γ q (TS γ q 1 s {⊤}) ht a r j y := by
  subst h h'
  exact ⟨LinearEquiv.ofBijective _ (hdg_res q s {⊤} (by simp) a has j), fun c b hc ha hb y => sqC_res γ q s ht har j c b hc ha hb y⟩

variable {E : Type} [CommRing E] (θ : B →+* E)

theorem main [CharZero K] (U : Cov q) {t : B} (ht : t ∈ I) (m : ℕ) (hker : RingHom.ker θ = I) (hp : ∀ r, pdP γ r = Ideal.span {t ^ r})
    (hnil : t ^ m = 0) (hgr : ∀ i < m, ∀ x : B, x * t ^ i ∈ Ideal.span {t ^ (i + 1)} → x ∈ I) (r j : ℕ) (hr : r < m) :
    Spans γ q (TS γ q 1 m {⊤}) ht r j ∧ ∃ co, IsCo γ q (TS γ q 1 m {⊤}) θ ht r j co := by
  have hm : pdP γ m = ⊥ := by rw [hp, hnil]; simp
  obtain ⟨S⟩ := split_field (K := K) γ m hm
  have hB : TFBase γ 1 m := ⟨hm, fun r x hx => by simpa using hx, fun n hn => ⟨0, algebraMap K B (n : K)⁻¹, by
    rw [pow_zero, ← map_natCast (algebraMap K B), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one]⟩⟩
  have ha := fun (i : Fin m) n => leC_shift γ q 1 m {⊤} i (S.ν i n) (S.mem i n) (r : ℤ)
  have hb := fun (i : Fin m) n => leC_shift γ q 1 m {⊤} i (S.ν i n) (S.mem i n) ((r : ℤ) + 1)
  have hT := bcOn_false γ 1 m m (tfBase_field K (by omega)) hB S q {⊤} (Or.inr ⟨not_false, ⟨U⟩, by simp⟩) (r : ℤ) ((r : ℤ) + 1)
    (by omega) (by omega) ha hb j
  let R : ∀ i : Fin m, S.N i → B → Prop := fun i n b => S.ν i n - b * t ^ (i : ℕ) ∈ pdP γ (i + 1)
  have h1 : ∀ i n, ∃ b, R i n b := fun i n => by
    have := S.mem i n
    rw [hp] at this
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨b, by simp only [R]; rw [hb, sub_self]; exact zero_mem _⟩
  have h2 : ∀ i b, ∃ n, R i n b := fun i b => by
    obtain ⟨n, hn⟩ := S.surj i (b * t ^ (i : ℕ)) (by rw [hp]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact ⟨n, by simpa using neg_mem hn⟩
  have hu : ∀ i n b b', R i n b → R i n b' → θ b = θ b' := fun i n b b' hb hb' => by
    have := sub_mem hb' hb
    rw [hp, show S.ν i n - b' * t ^ (i : ℕ) - (S.ν i n - b * t ^ (i : ℕ)) = (b - b') * t ^ (i : ℕ) by ring] at this
    have h0 := hgr i i.2 _ this
    rw [← hker, RingHom.mem_ker, map_sub] at h0
    exact sub_eq_zero.1 h0
  choose β hβ using h1
  let lam : ∀ i, S.N i →+ E := fun i => AddMonoidHom.mk' (fun n => θ (β i n)) fun n n' => by
    rw [← map_add (f := _)]
    refine hu i _ _ _ (hβ i _) ?_
    have := add_mem (hβ i n) (hβ i n')
    simp only [R, map_add (f := _)]
    convert this using 1; ring
  have h3 : ∀ i n b, R i n b → lam i n = θ b := fun i n b hb => hu i n _ _ (hβ i n) hb
  have hl : ∀ i (k : K) n, lam i (k • n) = θ (algebraMap K B k) * lam i n := fun i k n => by
    rw [h3 i (k • n) (algebraMap K B k * β i n), map_mul]
    · rfl
    · have := Ideal.mul_mem_left _ (algebraMap K B k) (hβ i n)
      simp only [R, map_smul, Algebra.smul_def]
      convert this using 1; ring
  have hE := fun (a : ℕ) (h : a ≤ r) => e_ex γ q m ht h (by omega) j ((r : ℤ) - ((r - a : ℕ) : ℤ)) ((r : ℤ) + 1 - ((r - a : ℕ) : ℤ))
    (by omega) (by omega)
  choose e he using hE
  obtain ⟨ind, co, c1, c2, c3⟩ := CoA.co_abs θ hr S.N (fun i => HQ (TO q 1 m {⊤}) ((r : ℤ) - i) ((r : ℤ) + 1 - i) j)
    (fun a => Hdg q a j) (fun a y => muG γ q (TS γ q 1 m {⊤}) ht a r j y) _ hT R lam hl (fun i n => ⟨_, hβ i n⟩) h2 h3
    (fun i hi => hq_zero _ _ _ (by omega) j) e (fun a h n b y hn => he a h _ b hn _ _ y)
  refine ⟨eq_top_iff.2 fun w _ => ?_, co, ?_, ?_, ?_, ?_, c3⟩
  · exact ind (fun w => w ∈ Submodule.span B {w : HG (TS γ q 1 m {⊤}) r j | ∃ a ≤ r, ∃ y, w = muG γ q (TS γ q 1 m {⊤}) ht a r j y})
      (zero_mem _) (fun _ _ => add_mem) (fun a h b y => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, y, rfl⟩)) w
  · intro b w a φ
    refine ind (fun w => co (b • w) a φ = θ b * co w a φ) (by simp) (fun x y hx hy => ?_) (fun a' h b' y => ?_) w
    · simp only [smul_add, map_add (f := _), Pi.add_apply, AddMonoidHom.add_apply, hx, hy, mul_add]
    · beta_reduce
      rw [smul_smul]
      by_cases h0 : a = a'
      · subst h0; rw [c1 a h, c1 a h, map_mul, mul_assoc]
      · rw [c2 a' h a h0, c2 a' h a h0]; simp
  · intro w a k φ
    refine ind (fun w => co w a (k • φ) = θ (algebraMap K B k) * co w a φ) (by simp) (fun x y hx hy => ?_) (fun a' h b' y => ?_) w
    · simp only [map_add (f := _), Pi.add_apply, AddMonoidHom.add_apply, hx, hy, mul_add]
    · beta_reduce
      by_cases h0 : a = a'
      · subst h0; rw [c1 a h, c1 a h, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul]; ring
      · rw [c2 a' h a h0]; simp
  · intro a h y φ
    have := c1 a h 1 y φ
    rwa [one_smul, map_one, one_mul] at this
  · intro a a' h y
    by_cases h' : a' ≤ r
    · have := c2 a' h' a h 1 y
      rwa [one_smul] at this
    · rw [mu_zero γ q _ ht (not_le.1 h'), map_zero]; rfl

end CoB

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

theorem coEx : CoEx l K := by
  intro Y m L M hM r j hr
  haveI := AdicGeo.proper_p hM.1
  haveI := hM.2
  obtain ⟨U⟩ := (cov_ex M.q).1 inferInstance
  exact CoB.main L.γB M.q L.θ U L.tB_mem m L.ker_θ L.pdB L.nil L.gr r j hr

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KFin
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.HT

theorem kFin : KFin := @kFin_of (@Pb.finO'.2)

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmulAbs
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb

namespace RhoA

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ok_dv (a : OK l K) (ha : a ≠ 0) : ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have ha' : (a : K) ≠ 0 := fun e => ha (Subtype.ext e)
  have h0 : 0 < ‖((a : K) : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast ha')
  have e : (((l : ℕ) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  have h1 : ‖(((l : ℕ) : K) : PadicAlgCl l)‖ < 1 := by
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one h0 h1
  refine ⟨k, ⟨(a : K)⁻¹ * (l : K) ^ k, (mem_OK _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow, norm_mul, norm_inv, norm_pow]
    rw [inv_mul_le_iff₀ h0, mul_one]
    exact hk.le
  · change (((l : OK l K) ^ k : OK l K) : K) = (a : K) * ((a : K)⁻¹ * (l : K) ^ k)
    rw [mul_inv_cancel_left₀ ha']
    simp

theorem tf_dom {O : Type} [CommRing O] [IsDomain O] [CharZero O] {l : ℕ} (hl : l ≠ 0)
    (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot O) l s := by
  have hb : ∀ r, 1 ≤ r → pdP (dividedPowersBot O) r = ⊥ := fun r hr => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    refine le_bot_iff.1 (le_trans ?_ (GlobalTheory.CompanionTheory.LiftLat.dividedPowerFiltration_one_eq (dividedPowersBot O)).le)
    refine Ideal.span_mono ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact ⟨L, h1, by omega, rfl⟩
  refine ⟨hb s hs, fun r x hx => ?_, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : (1 : O) ∈ pdP (dividedPowersBot O) 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
      simpa using Ideal.mul_mem_left _ x this
    · rw [hb r hr, Ideal.mem_bot] at hx ⊢
      exact (mul_eq_zero.1 hx).resolve_left (Nat.cast_ne_zero.2 hl)
  · obtain ⟨k, u, hu⟩ := hdv n (Nat.cast_ne_zero.2 hn)
    exact ⟨k, u, hu.symm⟩

section Abs
variable {A B Λ : Type} [CommRing A] [CommRing B] [CommRing Λ] {ι : A →+* B} {Z W : Type 1} [AddCommGroup Z] [Module A Z]
  [AddCommGroup W] [Module B W] (b : Z →ₛₗ[ι] W) {Zn : ℕ → Type 1} [∀ n, AddCommGroup (Zn n)] [∀ n, Module A (Zn n)]
  (red : ∀ n, Z →ₗ[A] Zn n) (l : ℕ)

theorem b_pow (e : ℕ) (z : Z) : b ((l : A) ^ e • z) = (l : B) ^ e • b z := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]

theorem exu (hu : IsUnit (l : B)) (x : ∀ n, Zn n) (e₀ : ℕ) (z₀ : Z) (h₀ : ∀ n, red n z₀ = (l : A) ^ e₀ • x n) (k : ℕ)
    (hs : ∀ z, (∀ n, red n z = 0) → (l : A) ^ k • z = 0) :
    ∃! w : W, ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z := by
  have key : ∀ (w w' : W) e z e' z', (∀ n, red n z = (l : A) ^ e • x n) → (l : B) ^ e • w = b z →
      (∀ n, red n z' = (l : A) ^ e' • x n) → (l : B) ^ e' • w' = b z' → w = w' := by
    intro w w' e z e' z' h1 h2 h3 h4
    have h5 := hs ((l : A) ^ e' • z - (l : A) ^ e • z') fun n => by
      rw [map_sub, map_smul, map_smul, h1, h3, smul_comm, sub_self]
    have h6 := congrArg b h5
    rw [b_pow, map_sub, b_pow, b_pow, ← h2, ← h4, map_zero, smul_comm ((l : B) ^ e) ((l : B) ^ e') w', ← smul_sub, ← smul_sub,
      smul_smul, smul_smul] at h6
    exact sub_eq_zero.1 (((((hu.pow k).mul (hu.pow e')).mul (hu.pow e)).smul_eq_zero).1 h6)
  obtain ⟨u, hu'⟩ := (hu.pow e₀).exists_right_inv
  have hw : (l : B) ^ e₀ • (u • b z₀) = b z₀ := by rw [smul_smul, hu', one_smul]
  exact ⟨u • b z₀, ⟨e₀, z₀, h₀, hw⟩, fun w ⟨e, z, h1, h2⟩ => key _ _ _ _ _ _ h1 h2 h₀ hw⟩

theorem add_abs (x y : ∀ n, Zn n) (w w' : W) (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z)
    (h' : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • y n) ∧ (l : B) ^ e • w' = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (x n + y n)) ∧ (l : B) ^ e • (w + w') = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  obtain ⟨e', z', h3, h4⟩ := h'
  refine ⟨e + e', (l : A) ^ e' • z + (l : A) ^ e • z', fun n => ?_, ?_⟩
  · rw [map_add (f := _), map_smul, map_smul, h1, h3, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : A) ^ e')]
  · rw [map_add (f := _), b_pow, b_pow, ← h2, ← h4, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : B) ^ e')]

theorem smul_abs (x : ∀ n, Zn n) (w : W) (a : A)
    (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (a • x n)) ∧ (l : B) ^ e • (ι a • w) = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  refine ⟨e, a • z, fun n => ?_, ?_⟩
  · rw [map_smul, h1, smul_comm]
  · rw [LinearMap.map_smulₛₗ, ← h2, smul_comm]

end Abs

variable {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

theorem unit_B : IsUnit (l : L.B) := by
  have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) : IsUnit (l : K)).map (algebraMap K L.B)
  rwa [map_natCast] at this

theorem rS_tr (r j n : ℕ) (x : CH.H (Y.SS M r (n + 1)).fn j) :
    (L.rS M r n).pull j ((pdOm (Y.redM M n) (RingHom.id _) (Y.rd_c n) r).pull j x) =
      trG (L.QA M) (l : L.A) n r j ((L.rS M r (n + 1)).pull j x) :=
  sub_trans (L.d (n + 1)) (L.d n) m {⊤} (Y.redM M n) (Y.c (n + 1)) (Y.c n) L.lam (L.d_lam (n + 1)) (L.d_lam n) (Y.rd_c n)
    (fun _ _ => rfl) (Y.c_surj (n + 1)) r j x

theorem ex [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (r j : ℕ) (hr : r < m) (x : Y.Fam M r j) (hx : CB.Comp x) : ∃! w, L.Rho x w := by
  haveI := AdicGeo.proper_p hM.1
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  obtain ⟨k, h1, h2⟩ := lift_gr afgA L.γ l m ok_dv (tf_dom (Fact.out : l.Prime).ne_zero ok_dv (by omega)) L.lat M.p U r hr j
  obtain ⟨z, hz⟩ := h1 (fun n => (L.rS M r n).pull j (x n)) fun n =>
    (rS_tr L M r j n (x (n + 1))).symm.trans (congrArg ((L.rS M r n).pull j) (hx n))
  exact exu (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l (unit_B L) (fun n => (L.rS M r n).pull j (x n))
    (2 * k) z hz k h2

theorem add (r j : ℕ) (x y : Y.Fam M r j) (w w' : HG (L.QB M) r j) (h : L.Rho x w) (h' : L.Rho y w') : L.Rho (x + y) (w + w') := by
  obtain ⟨e, z, h1, h2⟩ := add_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) (fun n => (L.rS M r n).pull j (y n)) w w' h h'
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (map_add ((L.rS M r n).pull j) (x n) (y n)).symm), h2⟩

theorem smul (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) (w : HG (L.QB M) r j) (h : L.Rho x w) : L.Rho (c • x) (L.ι (L.lam c) • w) := by
  obtain ⟨e, z, h1, h2⟩ := smul_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) w (L.lam c) h
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (LinearMap.map_smulₛₗ ((L.rS M r n).pull j) c (x n)).symm), h2⟩

end RhoA

theorem rhoEx {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K] : RhoEx l K := by
  exact ⟨fun L M => RhoA.ex L M, fun L M => RhoA.add L M, fun L M => RhoA.smul L M⟩

end CrystallineSemistableComparison.HT
end
end

