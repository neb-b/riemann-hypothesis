module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
section
noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsOpp (D : Datum H) (Z Z' : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ Z' ≤ perp D Z' ∧ (∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) ∧
    ∀ φ : Z' →+ ℤ, ∃! a : Z, ∀ b : Z', D.EF a b = φ b

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

def Cois (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) : Prop :=
  (∀ x, ∃ a e, y a = x + n • e) ∧
    ∀ a, (∀ b, (∃ e, y b = n • e) → (n : ℤ) ∣ D.EF a b) → ∃ e, y a = n • e

def KerIs (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (n : ℕ) : Prop :=
  ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e

abbrev img (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (I : Ideal (𝓞 E)) : Submodule (𝓞 E) X :=
  Z.map y ⊔ I • (⊤ : Submodule (𝓞 E) X)

def Improves (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (𝔭 : Ideal (𝓞 E)) (Z Z' Z'' : Submodule (𝓞 E) D.La) : Prop :=
  IsOpp D Z Z'' ∧ (∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → img D y Z' 𝔮 ≤ img D y Z'' 𝔮) ∧
    ¬ img D y Z'' 𝔭 ≤ img D y Z' 𝔭

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := H.starRing.star_involutive a

theorem ef_swap (D : Datum H) (a b : D.La) : D.EF a b = -D.EF b a := by
  have h := D.alt (a + b)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linear_combination h

theorem mem_perp {D : Datum H} {Z : Submodule (𝓞 E) D.La} {a : D.La} : a ∈ perp D Z ↔ ∀ z ∈ Z, D.EF a z = 0 := Iff.rfl

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.symm (h : IsOpp D Z Z') : IsOpp D Z' Z := by
  refine ⟨h.2.1, h.1, fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp
  · obtain ⟨a, ha, hu⟩ := h.2.2.1 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp

theorem IsOpp.eq_zero (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') (h0 : b ∈ perp D Z) : b = 0 := by
  obtain ⟨c, -, hu⟩ := h.2.2.1 0
  have h1 := hu ⟨b, hb⟩ fun a => by rw [ef_swap, h0 _ a.2]; simp
  have h2 := hu 0 fun a => by simp
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem IsOpp.exists_sub_mem_perp (h : IsOpp D Z Z') (a : D.La) : ∃ b ∈ Z', a - b ∈ perp D Z := by
  obtain ⟨b, hb, -⟩ := h.2.2.1 ((D.EF.flip a).toAddMonoidHom.comp Z.subtype.toAddMonoidHom)
  refine ⟨b, b.2, fun z hz => ?_⟩
  have := hb ⟨z, hz⟩
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, LinearMap.flip_apply] at this
  rw [ef_swap, map_sub, this]
  exact neg_eq_zero.2 (sub_self _)

theorem IsOpp.exists_decomp (h : IsOpp D Z Z') (a : D.La) :
    ∃ z ∈ Z, ∃ m ∈ perp D Z ⊓ perp D Z', ∃ b ∈ Z', a = z + m + b := by
  obtain ⟨b, hb, h1⟩ := h.exists_sub_mem_perp a
  obtain ⟨z, hz, h2⟩ := h.symm.exists_sub_mem_perp a
  refine ⟨z, hz, a - b - z, ⟨sub_mem h1 (h.1 hz), ?_⟩, b, hb, by abel⟩
  rw [sub_right_comm]
  exact sub_mem h2 (h.2.1 hb)

theorem IsOpp.isIsoSat (h : IsOpp D Z Z') : IsIsoSat D Z := by
  refine ⟨h.1, fun n x hn hx => ?_⟩
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp x
  have cancel : ∀ (W : Submodule (𝓞 E) D.La) (v : D.La), n • v ∈ perp D W → v ∈ perp D W := fun W v hv w hw => by
    have := hv w hw
    rw [map_nsmul, LinearMap.smul_apply, smul_eq_zero] at this
    exact this.resolve_left hn
  have hb0 : b = 0 := h.eq_zero hb (by
    have := sub_mem (cancel Z _ (h.1 hx)) (add_mem (h.1 hz) hm.1)
    rwa [add_sub_cancel_left] at this)
  subst hb0
  have hm0 : n • m = 0 := h.symm.eq_zero
    (by have := sub_mem hx (nsmul_mem hz n); rwa [add_zero, smul_add, add_sub_cancel_left] at this) (nsmul_mem hm.2 n)
  have : m = 0 := D.unimod.1 (LinearMap.ext fun w => by
    have := congrArg (fun v => D.EF v w) hm0
    simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_zero] at this
    simpa using this.resolve_left hn)
  simpa [this] using hz

theorem IsOpp.shear (h : IsOpp D Z Z') (t : Z' →ₗ[𝓞 E] D.La) (ht : ∀ b, t b - b ∈ perp D Z)
    (hiso : ∀ b b', D.EF (t b) (t b') = 0) : IsOpp D Z (LinearMap.range t) := by
  have key : ∀ (a : Z) (b : Z'), D.EF a (t b) = D.EF a b := fun a b => by
    have := ht b a a.2
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  refine ⟨h.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    exact hiso b b'
  · obtain ⟨b, hb, hu⟩ := h.2.2.1 φ
    refine ⟨⟨t b, b, rfl⟩, fun a => (key a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg t (hu b' fun a => (key a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (φ.comp t.rangeRestrict.toAddMonoidHom)
    refine ⟨a, ?_, fun a' ha' => hu a' fun b => (key a' b).symm.trans (ha' ⟨t b, b, rfl⟩)⟩
    rintro ⟨_, b, rfl⟩
    exact (key a b).trans (ha b)

theorem isOpp_bot (D : Datum H) : IsOpp D ⊥ ⊥ :=
  ⟨bot_le, bot_le, fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩,
    fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩⟩

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, GlobalTheory.CharRank.bar_rt_neg, map_ofNat] at h1
  have h2 := H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ (two_ne_zero (α := 𝓞 E)) (by linear_combination h1 + h2)

theorem exists_skew_solve (hd : ∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) (β : LinearMap.BilinForm ℤ Z)
    (hβ : ∀ a b, β a b = -β b a) (hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b)) :
    ∃ c : Z →ₗ[𝓞 E] Z', ∀ a b : Z, D.EF a (c b) + D.EF (c a) b = β a b := by
  choose c hc hu using fun b : Z => hd (AddMonoidHom.mk' (fun a => β (H.w0 • a) b) fun a a' => by simp)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  refine ⟨{ toFun := c, map_add' := fun b b' => (hu _ _ fun a => ?_).symm,
            map_smul' := fun x b => (hu _ _ fun a => ?_).symm }, fun a b => ?_⟩
  · simp [hc]
  · have h1 := hc b (H.bar x • a)
    rw [Submodule.coe_smul, D.adj, bar_bar, smul_comm, hadj, bar_bar] at h1
    exact h1
  · show D.EF a (c b) + D.EF (c a) b = _
    rw [ef_swap D (c a), hc, hc, ← hβ]
    have h2 := hadj (H.bar H.w0) a b
    rw [bar_bar] at h2
    rw [← h2, ← LinearMap.add_apply, ← map_add (f := _), ← add_smul, cmHostUnit_add_conj_eq_one, one_smul]

theorem IsOpp.exists_rank_one (h : IsOpp D Z Z') {m : D.La} (hm : m ∈ perp D Z ⊓ perp D Z') (θ : 𝓞 E →+ ℤ)
    (hθ : ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0) :
    ∃ ζ : (Z' →ₗ[𝓞 E] 𝓞 E) →+ D.La, (∀ ℓ, ζ ℓ ∈ Z) ∧ (∀ ℓ (x : Z'), D.EF x (ζ ℓ) = θ (ℓ x)) ∧
      (∀ (c : 𝓞 E) ℓ, ζ (c • ℓ) = H.bar c • ζ ℓ) ∧
      ∀ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, IsOpp D Z (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) := by
  choose z hz hu using fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => h.symm.2.2.1 (θ.comp ℓ.toAddMonoidHom)
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hz hu
  refine ⟨AddMonoidHom.mk' (fun ℓ => (z ℓ : D.La)) fun ℓ ℓ' => congrArg Subtype.val (hu _ (z ℓ + z ℓ') fun x => ?_).symm,
    fun ℓ => (z ℓ).2, hz, fun c ℓ => congrArg Subtype.val (hu _ (H.bar c • z ℓ) fun x => ?_).symm, fun ℓ => ?_⟩
  · simp [hz]
  · have := hz ℓ (c • x)
    rw [Submodule.coe_smul, D.adj, ℓ.map_smul] at this
    exact this
  · refine h.shear _ (fun b => ?_) fun b b' => ?_
    · simpa using (perp D Z).smul_mem (ℓ b) (add_mem hm.1 (h.1 (z ℓ).2))
    · have e1 : D.EF b b' = 0 := h.2.1 b.2 _ b'.2
      have e2 : ∀ (c : 𝓞 E) (x : Z'), D.EF (c • m) x = 0 := fun c x => (perp D Z').smul_mem c hm.2 _ x.2
      have e3 : ∀ c c' : 𝓞 E, D.EF (c • m) (c' • z ℓ) = 0 := fun c c' =>
        (perp D Z).smul_mem c hm.1 _ (Z.smul_mem c' (z ℓ).2)
      have e4 : ∀ c c' : 𝓞 E, D.EF (c • z ℓ) (c' • z ℓ) = 0 := fun c c' =>
        h.1 (Z.smul_mem c (z ℓ).2) _ (Z.smul_mem c' (z ℓ).2)
      have e5 : ∀ (c : 𝓞 E) (x : Z'), D.EF x (c • z ℓ) = θ (H.bar c * ℓ x) := fun c x => by
        have := hz ℓ (H.bar c • x)
        rw [Submodule.coe_smul, D.adj, bar_bar, ℓ.map_smul] at this
        exact this
      have e6 : D.EF (ℓ b • m) (ℓ b' • m) = D.EF ((H.bar (ℓ b') * ℓ b) • m) m := by
        rw [mul_smul, D.adj (H.bar (ℓ b')), bar_bar]
      have e7 := hθ (H.bar (ℓ b') * ℓ b)
      rw [map_mul H.bar, bar_bar, mul_comm (ℓ b')] at e7
      simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, AddMonoidHom.mk'_apply,
        smul_add, map_add]
      rw [ef_swap D b (ℓ b' • m), ef_swap D (ℓ b • (z ℓ : D.La)) b', ef_swap D (ℓ b • (z ℓ : D.La)) (ℓ b' • m),
        e1, e2, e2, e3, e3, e4, e5, e5, e6]
      linear_combination e7

theorem exists_theta_vec (D : Datum H) (m : D.La) :
    ∃ θ : 𝓞 E →+ ℤ, ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0 := by
  refine ⟨AddMonoidHom.mk' (fun t => -D.EF ((H.w0 * t) • m) m) fun a b => by simp [mul_add, add_smul, add_comm],
    fun t => ?_⟩
  have h1 : D.EF ((H.w0 * H.bar t) • m) m = -D.EF ((H.bar H.w0 * t) • m) m := by
    rw [D.adj, map_mul, bar_bar, ef_swap]
  have h2 : D.EF (t • m) m = D.EF ((H.w0 * t) • m) m + D.EF ((H.bar H.w0 * t) • m) m := by
    rw [← LinearMap.add_apply, ← map_add (f := _), ← add_smul, ← add_mul, cmHostUnit_add_conj_eq_one, one_mul]
  simp only [AddMonoidHom.mk'_apply]
  linear_combination h1 + h2

theorem range_le_of_mem {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (h : ∀ x, ℓ x ∈ I) :
    LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  refine sup_le ?_ le_sup_right
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem_smul (h x) trivial))

theorem range_le_of_ker {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (hI : I.IsMaximal) {v : P}
    (hv : f v ∈ I • (⊤ : Submodule O X)) (hl : ℓ v ∉ I) :
    u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) ∧
      LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  have hu : u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) := by
    obtain ⟨c, i, hi, hc⟩ := hI.exists_inv hl
    have : (f + ℓ.smulRight u) (c • v) - c • f v + i • u = u := by
      simp only [LinearMap.add_apply, map_smul, LinearMap.smulRight_apply, smul_add, add_sub_cancel_left, smul_smul]
      rw [← add_smul, hc, one_smul]
    have h2 : (f + ℓ.smulRight u) (c • v) - c • f v + i • u ∈
        LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) :=
      add_mem (sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hv)))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))
    rwa [this] at h2
  refine ⟨hu, sup_le ?_ le_sup_right⟩
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.smul_mem _ _ hu)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingHeatOperatorsActOnValues
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

namespace GlobalTheory.Heat

theorem ringOp_map_of_intertwine {A B : Type} [CommRing A] [CommRing B] (iK : A →+* B) {n : ℕ} (d : A → A) (dd : Fin n → A → A)
    (d' : B → B) (dd' : Fin n → B → B) (hd : ∀ w, d' (iK w) = iK (d w)) (hdd : ∀ a w, dd' a (iK w) = iK (dd a w))
    (Θ : Matrix (Fin n) (Fin n) A) (u : Fin n → A) (p p' : A) (k : ℕ) (f : A) :
    iK (ringOp d dd Θ u p p' k f) = ringOp d' dd' (iK.mapMatrix Θ) (fun a => iK (u a)) (iK p) (iK p') k (iK f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ringOp, map_sub, map_add (f := _), map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd,
    RingHom.mapMatrix_apply, Matrix.map_apply]

theorem ringOp_mul_of_const {K : Type} [CommRing K] {n : ℕ} (d : K → K) (δ : Fin n → K → K)
    (Θ : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (p p' : K) (k : ℕ) (c s : K)
    (hd : d (c * s) = c * d s + s * d c) (h1 : ∀ a y, δ a (c * y) = c * δ a y) :
    ringOp d δ Θ u p p' k (c * s) = c * ringOp d δ Θ u p p' k s + 2 * (k : K) * d c * s := by
  simp only [ringOp, h1, hd, mul_left_comm _ c, ← Finset.mul_sum]
  try ring

theorem exists_derivation_fractionRing_ext (Ω : Type) [CommRing Ω] [IsDomain Ω] (d : Derivation ℤ Ω Ω) :
    ∃ dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ w, dL (algebraMap Ω (FractionRing Ω) w) = algebraMap Ω (FractionRing Ω) (d w) := by
  obtain ⟨δ', hder, hδ'⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (nonZeroDivisors Ω) (B := FractionRing Ω)
    (fun w => algebraMap Ω (FractionRing Ω) (d w)) (fun a b => by simp)
    (fun a b => by simp [Derivation.leibniz, smul_eq_mul])
  have hsm : ∀ (z : ℤ) (a : FractionRing Ω), δ' (z • a) = z • δ' a := by
    intro z a
    induction z using Int.induction_on with
    | zero => simp [hder.der_zero]
    | succ i ih => simp only [add_smul, one_smul, hder.add, ih]
    | pred i ih => simp only [sub_smul, one_smul, hder.der_sub, ih]
  have hint : ∀ m : ℤ, δ' (m : FractionRing Ω) = 0 := fun m => by
    have := hsm m 1
    rw [zsmul_eq_mul, _root_.mul_one, hder.der_one] at this
    simpa using this
  have hlb : ∀ a b : FractionRing Ω, δ' (a * b) = a • δ' b + b • δ' a := fun a b => by
    rw [hder.mul, smul_eq_mul, smul_eq_mul]
  let dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω) := { toFun := δ', map_add' := hder.add, map_smul' := fun m y => by rw [RingHom.id_apply, Algebra.smul_def, eq_intCast, zsmul_eq_mul, hder.mul, hint m, MulZeroClass.mul_zero, add_zero], map_one_eq_zero' := hder.der_one, leibniz' := hlb }
  exact ⟨dL, hδ'⟩

theorem heat_acts_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmono htt hab
  intro Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg δL hδL
  letI := H.starRing
  have hDφ := (_root_.GlobalTheory.HeatPointValue.value_acts R Y.H _ _ P.D.toPre.P.L n dd ⇑D h i0 Ω φ x hx δ hδ dΩ hW hdΩ).1
  obtain ⟨e, p0, p0', hcore⟩ := GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring E H R t P m tt gam hmono htt hab Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω φ x x' δ
    hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg
  obtain ⟨dL, hdL⟩ := exists_derivation_fractionRing_ext Ω dΩ
  set iK := algebraMap Ω (FractionRing Ω) with hiK
  have hiKinj : Function.Injective iK := IsFractionRing.injective Ω (FractionRing Ω)
  have h2R : IsUnit (2 : R) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_ofNat] at this
  have h2K : (2 : FractionRing Ω) ≠ 0 := by
    have := (h2R.map (iK.comp φ)).ne_zero
    rwa [map_ofNat] at this
  have hsymm : ((iK.comp φ).mapMatrix h.Θ)ᵀ = (iK.comp φ).mapMatrix h.Θ := by
    show (h.Θ.map _)ᵀ = h.Θ.map _
    rw [← Matrix.transpose_map, h.symm]
  have hce : iK ((e⁻¹ : Ωˣ) : Ω) ≠ 0 := fun h0 => (e⁻¹).ne_zero (hiKinj (h0.trans (map_zero iK).symm))
  obtain ⟨d', u'', q, q', hd'c, hconj⟩ := _root_.GlobalTheory.Heat.ringOp_conj_pow Ω n dL δL ((iK.comp φ).mapMatrix h.Θ) hsymm h2K
    (fun a => iK (φ (h.u a))) (iK p0) (iK p0') _ hce
  refine ⟨d', u'', q, q', fun r => ?_, ?_⟩
  · rw [hd'c _ (fun a => by rw [hδL, hδφ, map_zero]), hdL, hDφ]
  intro k hk s ⟨r₁, σ, ω, hr₁, hv, hs⟩
  obtain ⟨r₂, σ₂, ω₂, hr₂, hv₂, hω₂⟩ := hcore k hk σ ω hv
  have key : iK ω₂ = iK (φ r₂) * ringOp ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK ω) := by
    rw [hω₂, map_mul, map_mul, map_pow, ringOp_map_of_intertwine iK _ _ _ _ hdL hδL, map_mul, map_pow]
    have e1 : iK.mapMatrix (φ.mapMatrix h.Θ) = (iK.comp φ).mapMatrix h.Θ := by
      ext a b; simp
    rw [e1, hconj, ← _root_.mul_assoc (iK (e : Ω) ^ k), ← mul_pow, ← map_mul, Units.mul_inv, map_one, one_pow, _root_.one_mul]
  by_cases hc1 : φ r₁ = 0
  · exact ⟨r₁, σ, ω, hr₁, hv, by rw [hs, hc1]; simp⟩
  · have hδc : ∀ a, δL a (iK (φ r₁)) = 0 := fun a => by rw [hδL, hδφ, map_zero]
    have hdc : d' (iK (φ r₁)) = iK (φ (D r₁)) := by rw [hd'c _ hδc, hdL, hDφ]
    have hs' : iK ω = iK (φ r₁) * s := hs
    have hRO := ringOp_mul_of_const ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK (φ r₁)) s
      (by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]) (fun a y => by
        rw [Derivation.leibniz, hδc, smul_zero, add_zero, smul_eq_mul])
    rw [← hs', hdc] at hRO
    obtain ⟨σ₃, hv₃⟩ := _root_.GlobalTheory.Heat.exists_isValue_lin R t.G t.PP.L Ω φ x' hx' g k σ₂ σ ω₂ ω r₁ (-(2 * (k : R)) * D r₁ * r₂) hv₂ hv
    refine ⟨r₁ * r₁ * r₂, σ₃, _, mul_ne_zero (mul_ne_zero hr₁ hr₁) hr₂, hv₃, ?_⟩
    simp only [RingHom.comp_apply, map_add (f := _), map_mul, map_neg, map_natCast, map_ofNat]
    rw [key, hRO, hs']
    ring

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateLogDerivMinusPotentialsChartIndependen
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
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem cancel_unit {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (δ : A → B) (u : Aˣ) (L Δ : B)
    (h₁ : δ u.val = π u.val * L) (h₂ : δ u.val = π u.val * Δ) : L = Δ :=
  ((Units.isUnit u).map π).mul_left_cancel (h₁.symm.trans h₂)

section ChartFreeProof

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} {h : Heat Y.H Y.q.left Q.P.L dd D}
  {K : Type} [Field K] {ν : R} {A₀ : Over (Sp K)} {m₀ : A₀.left ⟶ Q.P.A.left} {V : h.J → Q.P.A.left.Opens}
  {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}

theorem dE_trans_unit {D' : R → K} (hC : IsConnK Q.P.A Q.P.L A₀ m₀ D' V h.j ed pb) (hD : IsDesc Y h ν m₀ V ed pb)
    (hCo : Commutes Q m₀ ed) (α : Q.X) (j : Fin 4) (T : A₀.left ⟶ A₀.left) (h₁ : T ≫ m₀ = m₀ ≫ Q.famφB α j)
    (h₂ : T ≫ A₀.hom = A₀.hom) {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀)
    (z : Z) (i₀ : h.J) (hi₀ : (b ≫ m₀) z ∈ V i₀)
    (δ : Y.H.left.presheaf.stalk (a z) → Z.presheaf.stalk z)
    (hδ : ∀ W, W ≤ h.W i₀ → a z ∈ W → ∀ f, δ (gs (𝟙 _) (a z) W f) = gs a z W (dE h ν i₀ W f))
    (c c' : h.J) (hc : (b ≫ T ≫ m₀) z ∈ V c) (hc' : (b ≫ T ≫ m₀) z ∈ V c') :
    δ (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) (Q.P.L.g (h.j c) (h.j c')).val) =
      (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c'))
        (Q.P.L.g (h.j c) (h.j c')).val) *
        (gs (b ≫ T) z (m₀ ⁻¹ᵁ V c') (pb c') - gs (b ≫ T) z (m₀ ⁻¹ᵁ V c) (pb c)) := by
  have e : a ≫ Y.q.left ≫ Q.famφB α j = b ≫ T ≫ m₀ := by rw [h₁, reassoc_of% w]
  have hVL : V c ⊓ V c' ≤ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := inf_le_inf (hC.2.2.1 c) (hC.2.2.1 c')
  have hpV : (Q.famφB α j) (Y.q.left (a z)) ∈ V c ⊓ V c' := by
    show (a ≫ Y.q.left ≫ Q.famφB α j) z ∈ V c ⊓ V c'
    rw [e]; exact ⟨hc, hc'⟩
  have hq0 : Y.q.left (a z) ∈ V i₀ := by
    show (a ≫ Y.q.left) z ∈ V i₀
    rw [w]; exact hi₀
  have hqU : Y.q.left (a z) ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := ⟨hq0, hpV⟩
  have hbU : (b ≫ m₀) z ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := by
    show (b ≫ m₀) z ∈ _
    rw [← w]; exact hqU
  set g := (Q.P.L.g (h.j c) (h.j c')).val
  set F := ((Q.famφB α j).app (V c ⊓ V c')).hom (rsT g (V c ⊓ V c'))
  set f := resG Q.P.A.left (inf_le_right : V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') ≤ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) F
  have s₁ : gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) g =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c'))) ((Y.q.left.app _).hom f) := by
    rw [gs_pull (𝟙 _) Y.q.left (a z) _ hqU f, Category.id_comp, gs_res Y.q.left (a z) inf_le_right hqU F,
      gs_pull Y.q.left (Q.famφB α j) (a z) _ hpV _, gs_rsT (Y.q.left ≫ Q.famφB α j) (a z) hVL hpV]
  have hle : Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ h.W i₀ := by
    rw [hD.1 i₀]; exact fun _ hx ↦ hx.1
  have hbT : (b ≫ T) z ∈ m₀ ⁻¹ᵁ (V c ⊓ V c') := ⟨hc, hc'⟩
  have m : (Y.q.left ≫ Q.famφB α j) (a z) ∈ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := hVL hpV
  have hπ : (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) _ g) = gs (b ≫ T ≫ m₀) z _ g := by
    rw [← e, ← gs_pull a (Y.q.left ≫ Q.famφB α j) z _ m g, gs_stalkMap a z _ m, gs_pull (𝟙 _) _ (a z) _ m g,
      Category.id_comp]
  rw [hπ, s₁, hδ _ hle hqU, ← hD.2.1 Z a b w z i₀ _ inf_le_left hbU f,
    hC.1.res _ _ inf_le_right le_top F, gs_rsT b z (show m₀ ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ m₀ ⁻¹ᵁ (Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) from fun _ hx ↦ hx.2) hbU,
    hCo α j T h₁ h₂ (V c ⊓ V c') (rsT g (V c ⊓ V c')) Z b z ⟨hc, hc'⟩, hC.2.2.2 c c',
    gs_mul _ z _ hbT, gs_sub _ z _ hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c' from fun _ hx ↦ hx.2) hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c from fun _ hx ↦ hx.1) hbT,
    gs_pbT (b ≫ T) m₀ z (fun _ hx ↦ hVL hx) hbT, Category.assoc]

end ChartFreeProof

theorem chartFree : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCo α T h₁ h₂ Z a b hw z i i' hi hi' w H
  unfold CoordAt at H ⊢
  have hV : ∀ c, V c ≤ Q.P.L.U (h.j c) := hC.2.2.1
  have hm := hF.mem_chart hD hV h₁ hw hi
  have hm' := hF.mem_chart hD hV h₁ hw hi'
  have hT0 := hF.T_zero (h₁ 0) (h₂ 0)
  have hi₀ : (b ≫ m₀) z ∈ V (i 0) := by
    have := hi 0
    rwa [hT0, Category.id_comp] at this
  obtain ⟨δ, -, hδm, hδ⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z hm.1
  obtain ⟨l, hl⟩ := exists_dlog (a.stalkMap z).hom δ hδm
  have hx : gs a z (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j))
      (dE h ν (i 0) _ (rsT (xc Y α fun j ↦ h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i j)) (xc Y α fun j ↦ h.j (i j))).val := by
    rw [← hδ _ inf_le_left hm, gs_rsT (𝟙 _) (a z) inf_le_right hm, gs_unit (𝟙 _) (a z) _ hm.2]
  have hx' : gs a z (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j))
      (dE h ν (i' 0) _ (rsT (xc Y α fun j ↦ h.j (i' j)).val (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i' j)) (xc Y α fun j ↦ h.j (i' j))).val := by
    have hU : a z ∈ h.W (i 0) ⊓ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) := ⟨⟨hm.1, hm'.1⟩, hm'.2⟩
    have hle : h.W (i 0) ⊓ h.W (i' 0) ⊓ (xU Y α fun j ↦ h.j (i' j)) ≤ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) :=
      fun _ hy ↦ ⟨hy.1.2, hy.2⟩
    rw [← gs_res a z hle hU, ← (isField_dE h ν hF.field (i' 0)).2.2 _ _ hle inf_le_left,
      ← hF.dE_agree hw z (i 0) (i' 0) _ inf_le_left hU, ← hδ _ (inf_le_left.trans inf_le_left) hU, gs_res (𝟙 _) (a z) hle hU,
      gs_rsT (𝟙 _) (a z) inf_le_right hm', gs_unit (𝟙 _) (a z) _ hm'.2]
  have ht := gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 Y.H.left) (a z) hm.2 hm'.2
  have hu : ∀ k, (l (gm (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z)
      (Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))))
      (Q.P.L.g (h.j (i (![1, 2, 0, 3] k))) (h.j (i' (![1, 2, 0, 3] k)))))).toAdd =
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i' (![1, 2, 0, 3] k))) (pb (i' (![1, 2, 0, 3] k))) -
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i (![1, 2, 0, 3] k))) (pb (i (![1, 2, 0, 3] k))) := by
    intro k
    have mem : (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z) ∈
        Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))) :=
      ⟨Set.mem_iInter.1 hm.2 k, Set.mem_iInter.1 hm'.2 k⟩
    refine cancel_unit _ δ _ _ _ (hl _) ?_
    rw [← gs_unit _ _ _ mem, Category.id_comp, gtφT_eq]
    exact dE_trans_unit hC hD hCo α _ (T _) (h₁ _) (h₂ _) hw z (i 0) hi₀ δ hδ _ _ (hi _) (hi' _)
  have e2 := congrArg (fun u ↦ (l u).toAdd) ht
  simp only [map_mul, toAdd_mul, trF, map_prod, map_zpow, toAdd_prod, toAdd_zpow, Fin.sum_univ_four] at e2
  rw [hu 0, hu 1, hu 2, hu 3] at e2
  simp only [DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e2
  rw [hx, gs_stalkMap a z _ hm.2, gs_unit (𝟙 _) (a z) _ hm.2] at H
  have eH := cancel_unit _ δ _ _ _ (hl _) H
  rw [hx', hl, gs_stalkMap a z _ hm'.2, gs_unit (𝟙 _) (a z) _ hm'.2]
  congr 1
  linear_combination eH - e2

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivStrictHenselianLinePointStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ, Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i) := by
  first | (exact @GlobalTheory.EtC.LineLocal.eqv_local) | (exact GlobalTheory.EtC.LineLocal.eqv_local) | (intros; apply GlobalTheory.EtC.LineLocal.eqv_local  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexUniformisation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.Unif.exists_unifAt) | (exact GlobalTheory.UPel.HT.Unif.exists_unifAt) | (intros; apply GlobalTheory.UPel.HT.Unif.exists_unifAt <;> assumption)
end

