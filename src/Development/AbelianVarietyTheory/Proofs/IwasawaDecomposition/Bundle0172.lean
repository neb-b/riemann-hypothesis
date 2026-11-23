module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfUpSumOfNorm
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpInj

variable {R V k W : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W]
  {res : R →+* k} {t : R} {Λ : Submodule R V} {π : V → W}

def Rel (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (q : Pr R V k) (w : W) : Prop :=
  q.Ok res ∧ q.IsKer Λ ∧ ∃ e, q.f e = 1 ∧ π (t • e) = w

theorem mem_of_one {q : Pr R V k} (h : q.Ok res) {e : V} (he : q.f e = 1) : e ∈ q.L := by
  by_contra hn
  rw [h.off e hn] at he
  exact zero_ne_one he

theorem f_sub {q : Pr R V k} (h : q.Ok res) {x y : V} (hx : x ∈ q.L) (hy : y ∈ q.L) :
    q.f (x - y) = q.f x - q.f y := by
  have := h.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem pi_sub (h : Red res t Λ π) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) : π (x - y) = π x - π y := by
  have := h.add (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem te_mem (ht : res t = 0) {q : Pr R V k} (h : q.Ok res) (hk : q.IsKer Λ) {e : V} (he : e ∈ q.L) :
    t • e ∈ Λ :=
  (hk _).2 ⟨q.L.smul_mem _ he, by rw [h.smul _ _ he, ht, zero_mul]⟩

theorem mem_of_pi (htf : ∀ x : V, t • x = 0 → x = 0) (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ)
    (hr : Red res t Λ π) {x : V} (hx : t • x ∈ Λ) (h0 : π (t • x) = 0) : x ∈ Λ := by
  obtain ⟨y, hy, s, hs, h⟩ := (hr.ker _ hx).1 h0
  have : s • x - y = 0 := htf _ (by rw [smul_sub, smul_comm, h, sub_self])
  exact hsat s x hs (by rw [sub_eq_zero.1 this]; exact hy)

theorem rel_fun (ht : res t = 0) (hr : Red res t Λ π) {q : Pr R V k} {w w' : W}
    (h : Rel res t Λ π q w) (h' : Rel res t Λ π q w') : w = w' := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨-, -, e', he', rfl⟩ := h'
  have m := mem_of_one ho he
  have m' := mem_of_one ho he'
  have h1 : e - e' ∈ Λ := (hk _).2 ⟨sub_mem m m', by rw [f_sub ho m m', he, he', sub_self]⟩
  have h2 := hr.smul t _ h1
  rw [ht, zero_smul, smul_sub, pi_sub hr (te_mem ht ho hk m) (te_mem ht ho hk m')] at h2
  exact sub_eq_zero.1 h2

theorem le_of_sub (hs : Function.Surjective res) {q q' : Pr R V k} (ho : q.Ok res) (hk : q.IsKer Λ)
    (ho' : q'.Ok res) (hk' : q'.IsKer Λ) {e e' : V} (he : q.f e = 1) (he' : q'.f e' = 1) (h : e - e' ∈ Λ)
    (y : V) (hy : y ∈ q.L) : y ∈ q'.L ∧ q'.f y = q.f y := by
  have m := mem_of_one ho he
  have m' := mem_of_one ho' he'
  obtain ⟨a, ha⟩ := hs (q.f y)
  have h1 : y - a • e ∈ Λ := (hk _).2 ⟨sub_mem hy (q.L.smul_mem _ m), by
    rw [f_sub ho hy (q.L.smul_mem _ m), ho.smul _ _ m, he, ha, mul_one, sub_self]⟩
  have h2 : y - a • e' ∈ Λ := by
    have := add_mem h1 (Λ.smul_mem a h)
    rwa [smul_sub, sub_add_sub_cancel] at this
  obtain ⟨h3, h4⟩ := (hk' _).1 h2
  have h5 : y ∈ q'.L := by
    have := add_mem h3 (q'.L.smul_mem a m')
    rwa [sub_add_cancel] at this
  refine ⟨h5, ?_⟩
  rw [f_sub ho' h5 (q'.L.smul_mem _ m'), ho'.smul _ _ m', he', mul_one, ha] at h4
  exact sub_eq_zero.1 h4

theorem rel_inj (hs : Function.Surjective res) (ht : res t = 0) (htf : ∀ x : V, t • x = 0 → x = 0)
    (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) (hr : Red res t Λ π) {q q' : Pr R V k} {w : W}
    (h : Rel res t Λ π q w) (h' : Rel res t Λ π q' w) : q = q' := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨ho', hk', e', he', hw⟩ := h'
  have m := te_mem ht ho hk (mem_of_one ho he)
  have m' := te_mem ht ho' hk' (mem_of_one ho' he')
  have h1 : e - e' ∈ Λ := mem_of_pi htf hsat hr (by rw [smul_sub]; exact sub_mem m m')
    (by rw [smul_sub, pi_sub hr m m', hw, sub_self])
  have h2 : e' - e ∈ Λ := by rw [← neg_sub]; exact neg_mem h1
  have A := le_of_sub hs ho hk ho' hk' he he' h1
  have B := le_of_sub hs ho' hk' ho hk he' he h2
  ext y
  · exact ⟨fun h => (A y h).1, fun h => (B y h).1⟩
  · by_cases hy : y ∈ q.L
    · exact (A y hy).2.symm
    · rw [ho.off y hy, ho'.off y (fun h => hy (B y h).1)]

theorem rel_ne (ht : res t = 0) (htf : ∀ x : V, t • x = 0 → x = 0)
    (hsat : ∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) (hr : Red res t Λ π) (q : Pr R V k) :
    ¬ Rel res t Λ π q 0 := by
  rintro ⟨ho, hk, e, he, h⟩
  have := ((hk _).1 (mem_of_pi htf hsat hr (te_mem ht ho hk (mem_of_one ho he)) h)).2
  rw [he] at this
  exact one_ne_zero this

theorem rel_ex (hs : Function.Surjective res) {q : Pr R V k} (ho : q.Ok res) (hk : q.IsKer Λ) :
    ∃ w, Rel res t Λ π q w := by
  obtain ⟨x, hx⟩ := ho.ne
  have m : x ∈ q.L := by
    by_contra hn
    exact hx (ho.off x hn)
  obtain ⟨a, ha⟩ := hs (q.f x)⁻¹
  exact ⟨_, ho, hk, a • x, by rw [ho.smul _ _ m, ha, inv_mul_cancel₀ hx], rfl⟩

theorem rel_dil (hs : Function.Surjective res) (ht : res t = 0) (hr : Red res t Λ π) {q : Pr R V k} {w : W}
    (h : Rel res t Λ π q w) {a : k} (ha : a ≠ 0) : Rel res t Λ π (q.dil a⁻¹) (a • w) := by
  obtain ⟨ho, hk, e, he, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  have m := mem_of_one ho he
  refine ⟨ho.dil (inv_ne_zero ha), fun y => ?_, b • e, ?_, ?_⟩
  · rw [hk y]
    show _ ↔ y ∈ q.L ∧ (res b)⁻¹ * q.f y = 0
    simp [ha]
  · show (res b)⁻¹ * q.f (b • e) = 1
    rw [ho.smul _ _ m, he, mul_one, inv_mul_cancel₀ ha]
  · rw [smul_comm, hr.smul _ _ (te_mem ht ho hk m)]

end GlobalTheory.LevelHecke.UpInj

namespace GlobalTheory.LevelHecke


open UpInj in
theorem eq_zero_of_upSum_of_norm : ∀ (R V k W M : Type) [CommRing R] [AddCommGroup V] [Module R V] [Field k] [AddCommGroup W] [Module k W] [Fintype k] [DecidableEq k] [Finite W] [AddCommGroup M] [Module ℂ M] (res : R →+* k) (t : R) (Λ : Submodule R V) (π : V → W) (Φ : Pr R V k → M), Function.Surjective res → res t = 0 → (∀ x : V, t • x = 0 → x = 0) → (∀ s x, res s ≠ 0 → s • x ∈ Λ → x ∈ Λ) → Red res t Λ π → (∀ g : Module.Dual k W, g ≠ 0 → ∃ d : Pr R V k, d.L = Λ ∧ (∀ x ∈ Λ, d.f x = g (π x)) ∧ ∑ᶠ q ∈ {q | Pr.Inc res t d q}, Φ q = 0) → (∀ q : Pr R V k, q.Ok res → q.IsKer Λ → ∑ a : kˣ, Φ (q.dil (a : k)) = 0) → ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Φ q = 0 := by
  intro R V k W M _ _ _ _ _ _ _ _ _ _ _ res t Λ π Φ hs ht htf hsat hr hup hnm
  classical
  let ψ : W → M := fun w => if h : ∃ q, Rel res t Λ π q w then Φ h.choose else 0
  have ψ1 : ∀ q w, Rel res t Λ π q w → ψ w = Φ q := fun q w h => by
    have h0 : ∃ q, Rel res t Λ π q w := ⟨q, h⟩
    simp only [ψ, dif_pos h0]
    rw [rel_inj hs ht htf hsat hr h0.choose_spec h]
  have ψ0 : ∀ w, (¬ ∃ q, Rel res t Λ π q w) → ψ w = 0 := fun w h => dif_neg h
  let j : Pr R V k → W := fun q => if h : ∃ w, Rel res t Λ π q w then h.choose else 0
  have j1 : ∀ q : Pr R V k, q.Ok res → q.IsKer Λ → Rel res t Λ π q (j q) := fun q ho hk => by
    have h0 : ∃ w, Rel res t Λ π q w := rel_ex hs ho hk
    simp only [j, dif_pos h0]
    exact h0.choose_spec
  have key := GlobalTheory.T.eq_zero_of_affineHyperplane_line_sums k W M ψ (ψ0 _ fun ⟨q, h⟩ => rel_ne ht htf hsat hr q h) (fun g hg => ?_) (fun w => ?_)
  · intro q ho hk
    rw [← ψ1 q _ (j1 q ho hk)]
    exact key _
  · obtain ⟨d, rfl, hd, hsum⟩ := hup g hg
    have hinj : Set.InjOn j {q | Pr.Inc res t d q} := fun q hq q' hq' h =>
      rel_inj hs ht htf hsat hr (j1 q hq.1 hq.2.1) (h ▸ j1 q' hq'.1 hq'.2.1)
    have e1 : ∑ᶠ x ∈ {x | g x = 1}, ψ x = ∑ᶠ x ∈ j '' {q | Pr.Inc res t d q}, ψ x := by
      apply finsum_mem_inter_support_eq'
      intro w hw
      have hex : ∃ q, Rel res t d.L π q w := by
        by_contra hn
        exact hw (ψ0 w hn)
      obtain ⟨q, hq⟩ := hex
      constructor
      · intro hg1
        refine ⟨q, ?_, rel_fun ht hr (j1 q hq.1 hq.2.1) hq⟩
        obtain ⟨ho, hk, e, he, rfl⟩ := hq
        exact ⟨ho, hk, e, he, by rw [hd _ (te_mem ht ho hk (mem_of_one ho he))]; exact hg1⟩
      · rintro ⟨q', ⟨ho, hk, e, he, h1⟩, rfl⟩
        rw [hd _ (te_mem ht ho hk (mem_of_one ho he))] at h1
        show g _ = 1
        rw [rel_fun ht hr (j1 q' ho hk) ⟨ho, hk, e, he, rfl⟩]
        exact h1
    rw [e1, finsum_mem_image hinj, ← hsum]
    exact finsum_mem_congr rfl fun q hq => ψ1 q _ (j1 q hq.1 hq.2.1)
  · by_cases hex : ∃ q, Rel res t Λ π q w
    · obtain ⟨q, hq⟩ := hex
      rw [← hnm q hq.1 hq.2.1, ← Equiv.sum_comp (Equiv.inv kˣ)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := ψ1 _ _ (rel_dil hs ht hr hq (a⁻¹).ne_zero)
      rw [Units.val_inv_eq_inv_val, inv_inv] at this
      rw [← this, Equiv.inv_apply, Units.val_inv_eq_inv_val]
    · refine Finset.sum_eq_zero fun a _ => ψ0 _ ?_
      rintro ⟨q, hq⟩
      have := rel_dil hs ht hr hq (inv_ne_zero a.ne_zero)
      rw [smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul] at this
      exact hex ⟨_, this⟩

end GlobalTheory.LevelHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitary
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open Formalism.UG (cT cT_mul cT_one bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeRef

section Cong

variable {A : Type} [CommRing A] {M : ℕ} (s : A →+* A)

def act (J : Matrix (Fin M) (Fin M) A) (P : GL (Fin M) A) : Matrix (Fin M) (Fin M) A :=
  cT s (P : Matrix (Fin M) (Fin M) A) * J * (P : Matrix (Fin M) (Fin M) A)

theorem act_one (J : Matrix (Fin M) (Fin M) A) : act s J 1 = J := by
  simp [act, cT_one]

theorem act_mul (J : Matrix (Fin M) (Fin M) A) (P Q : GL (Fin M) A) :
    act s J (P * Q) = act s (act s J P) Q := by
  simp only [act, Units.val_mul, cT_mul, Matrix.mul_assoc]

def cong (M : ℕ) : Setoid (Matrix (Fin M) (Fin M) A) where
  r J J' := ∃ P : GL (Fin M) A, J' = act s J P
  iseqv := ⟨fun J => ⟨1, (act_one s J).symm⟩,
    fun ⟨P, h⟩ => ⟨P⁻¹, by rw [h, ← act_mul, mul_inv_cancel, act_one]⟩,
    fun ⟨P, h⟩ ⟨Q, h'⟩ => ⟨P * Q, by rw [h', h, act_mul]⟩⟩

end Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}

omit [NumberField E] in
theorem frameRel_iff (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (g : HA (AF F) σ J)
    (g' : HA (AF F) σ J') : FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g g' ↔
      HA.mat (AF F) σ J' g' = (bc (inclR (AF F)) P)⁻¹ * HA.mat (AF F) σ J g * bc (inclR (AF F)) P := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm, ← Units.val_inj]
  rfl

omit [NumberField E] in
theorem bc_mem {J : Matrix (Fin M) (Fin M) E} {u : GL (Fin M) E} (hu : act (σ : E →+* E) J u = J) :
    bc (inclR (AF F)) u ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (u : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  have h : cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR, inclR]
  rw [h, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun X : Matrix (Fin M) (Fin M) E => X.map (inclR (F := F) (AF F))) hu

def IsTransport (σ : E →ₐ[F] E) (J₀ J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)) : Prop :=
  ∃ (P : GL (Fin M) E) (e : HA (AF F) σ J₀ ≃* HA (AF F) σ J), J = act (σ : E →+* E) J₀ P ∧
    (∀ g, FrameRel J₀ J (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ μ = Measure.haar.map e

theorem frame (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (h : J' = act (σ : E →+* E) J P) :
    (∃ e : HA (AF F) σ J ≃* HA (AF F) σ J', ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧
    ∀ e : HA (AF F) σ J ≃* HA (AF F) σ J', (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) →
      Continuous e ∧ Continuous e.symm :=
  ⟨(_root_.GlobalTheory.GaugeFrameBasis.frame_basis F E σ (AF F) M J J' P h).1.exists, (_root_.GlobalTheory.GaugeFrameBasis.frame_basis F E σ (AF F) M J J' P h).2⟩

theorem IsTransport.isHaar {J₀ J : Matrix (Fin M) (Fin M) E} {μ : Measure (HA (AF F) σ J)}
    (h : IsTransport σ J₀ J μ) : μ.IsHaarMeasure := by
  obtain ⟨P, e, hJ, he, rfl⟩ := h
  obtain ⟨h1, h2⟩ := (frame J₀ J P hJ).2 e he
  exact e.isHaarMeasure_map _ h1 h2

theorem IsTransport.map_eq (hσ : IsCMExt F E σ) {J₀ J J' : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : IsTransport σ J₀ J μ) (h' : IsTransport σ J₀ J' μ') {P : GL (Fin M) E} (hP : J' = act (σ : E →+* E) J P)
    (e : HA (AF F) σ J ≃* HA (AF F) σ J') (he : ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) :
    μ.map e = μ' := by
  haveI := h.isHaar
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (GlobalTheory.HermLineZeros.conj_invol hσ) (δ := σ d - d)
      (sub_ne_zero.2 hd) (by rw [map_sub, GlobalTheory.HermLineZeros.conj_invol hσ, neg_sub]) hJ μ
  obtain ⟨P₁, e₁, hJ₁, he₁, hμ⟩ := h
  obtain ⟨P₂, e₂, hJ₂, he₂, rfl⟩ := h'
  have hu : act (σ : E →+* E) J (P₁⁻¹ * P₂ * P⁻¹) = J := by
    conv_lhs => rw [hJ₁, ← act_mul, ← mul_assoc, mul_inv_cancel_left, act_mul, ← hJ₂, hP, ← act_mul,
      mul_inv_cancel, act_one]
  let u : HA (AF F) σ J := (⟨_, bc_mem hu⟩ : HR (AF F) σ J)
  have hc := ((frame J J' P hP).2 e he).1.measurable
  have hc₁ := ((frame J₀ J P₁ hJ₁).2 e₁ he₁).1.measurable
  have key : (e₂ : _ → _) = e ∘ ((fun x => x * u) ∘ (fun x => u⁻¹ * x)) ∘ e₁ := by
    funext g
    apply Subtype.ext
    have a := (frameRel_iff _ _ _ _ _).1 (he₂ g)
    have b := (frameRel_iff _ _ _ _ _).1 (he (u⁻¹ * e₁ g * u))
    have c := (frameRel_iff _ _ _ _ _).1 (he₁ g)
    refine a.trans (Eq.trans ?_ b.symm)
    show _ = _ * ((bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹))⁻¹ * HA.mat (AF F) σ J (e₁ g) *
      bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹)) * _
    rw [c]
    simp only [map_mul, map_inv]
    group
  have hl := measurable_const_mul u⁻¹
  have hr := measurable_mul_const u
  rw [key, ← Measure.map_map hc ((hr.comp hl).comp hc₁), ← Measure.map_map (hr.comp hl) hc₁, ← hμ,
    ← Measure.map_map hr hl, map_mul_left_eq_self, map_mul_right_eq_self]

theorem exists_isTransport (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    ∃ μ, IsTransport σ (Quotient.mk (cong (σ : E →+* E) M) J).out J μ := by
  obtain ⟨P, hP⟩ := Quotient.mk_out (s := cong (σ : E →+* E) M) J
  obtain ⟨e, he⟩ := (frame (σ := σ) _ J P hP).1
  exact ⟨_, P, e, hP, he, rfl⟩

theorem exists_isHaar_basisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  intro F E _ _ _ _ _ σ hσ
  choose μ hμ using fun (M : ℕ) (J : Matrix (Fin M) (Fin M) E) => exists_isTransport σ J
  refine ⟨⟨μ⟩, fun M J _ => (hμ M J).isHaar, fun M J J' P hJ hP => ⟨(frame J J' P hP).1, fun e he => ?_⟩⟩
  have h' := hμ M J'
  rw [← Quotient.sound (s := cong (σ : E →+* E) M) (a := J) (b := J') ⟨P, hP⟩] at h'
  exact (hμ M J).map_eq hσ hJ h' hP e he

end GlobalTheory.GaugeRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR.Links
  Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharTransport

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locMap_eq (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F) :
    GlobalTheory.AdeleBaseChange.locMap F P a = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a := by
  refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val P _ fun n => ?_)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap F E P
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le (P.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)
  have h2 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-(n : ℤ))).preimage
    ((continuous_sub_left (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a)).comp hc)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F)
    (P.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩
  have e : GlobalTheory.AdeleBaseChange.locMap F P a - GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a =
      GlobalTheory.AdeleBaseChange.locMap F P (a - algebraMap F _ k) -
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a -
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P (algebraMap F _ k)) := by
    rw [map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    ring
  rw [e]
  exact Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk1) hk2

theorem exists_toAdele : ∃ Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E, Continuous Θ ∧
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (AdeleRing (𝓞 E) E) :=
    ((algebraMap E (AdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] AdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : AF F →ₐ[F] AdeleRing (𝓞 E) E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E, fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x⟩
  let Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E := (Algebra.TensorProduct.productMap g f).toRingHom
  have hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x := fun a x => rfl
  refine ⟨Θ, ?_, hΘ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let φ : AF F ⊗[F] E →ₛₗ[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E] AdeleRing (𝓞 E) E :=
    { toFun := Θ
      map_add' := map_add Θ
      map_smul' := fun r z => by
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        change Θ (r ⊗ₜ[F] 1) = _
        rw [hΘ, map_one, mul_one] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap F E) φ

end General

theorem isDelta_of_isPlIdem {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΦ : GlobalTheory.IdemSupport.Comp D Φ) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : IsPlIdem D e P) :
    GlobalTheory.IdemSupport.IsDelta Φ P e := by
  obtain ⟨h1, ⟨v, ε, hε, h2⟩, ht⟩ := h
  refine (GlobalTheory.IdemSupport.tie_iff hΦ h1 ?_ P).1 ht
  rcases h2 with ⟨h2, h3⟩ | h2
  · have : e = (e + cA D e) * e := by linear_combination -h1 - h2
    rw [this, h3, RingHom.map_mul, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, zero_mul]
  · rw [h2, (GlobalTheory.IdemSupport.place_comp hΦ hε).1]

theorem map_loc {A B : Type} [Ring A] [Ring B] (f : A →+* B) (e k : A) :
    f (1 + e * (k - 1)) = 1 + f e * (f k - 1) := by
  rw [map_add (f := _), map_mul, map_sub, map_one]


set_option maxHeartbeats 800000 in
theorem exists_hom (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem exists_chrEq : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.IsUnitary → ∃ c, ChrEq c χ := by
  intro D χ hχ
  obtain ⟨Θ, hc, hinc, hloc⟩ := exists_hom D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c, ⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
    rw [hcoe, this, χ.2.2]
    rfl
  · have : u x = localIdele D.host.E P (atFin P k) := by
      refine Units.ext ?_
      change Θ (x : AE D) = _
      rw [hx, hloc P e he]
    rw [hcoe, this]
    rfl

end GlobalTheory.CharTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_section_compatible_square_thickening : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  first | exact @GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | exact GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq | (intros; apply GlobalTheory.SectionLimitSq.existsUnique_sec_of_compatible_sq <;> assumption)
end

