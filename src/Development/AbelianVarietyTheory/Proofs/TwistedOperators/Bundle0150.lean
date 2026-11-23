module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.UnramFixed

theorem occursTimes_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ θ η : G →* ℂˣ} (h : ∀ g v, τ g v = (δ g : ℂ) • ρ g v)
    (hη : ∀ g, η g = θ g * δ g) {r : ℕ} (hr : OccursTimes (ofChar θ) ρ r) :
    OccursTimes (ofChar η) τ r := by
  obtain ⟨S, T, h1, h2, h3⟩ := hr
  have hst : ∀ (P : Subrepresentation ρ) (g : G) (v : V), v ∈ P.toSubmodule → τ g v ∈ P.toSubmodule :=
    fun P g v hv => by
      rw [h]
      exact P.toSubmodule.smul_mem _ (P.apply_mem_toSubmodule g hv)
  refine ⟨fun i => ⟨(S i).toSubmodule, hst (S i)⟩, fun i => ⟨(T i).toSubmodule, hst (T i)⟩,
    fun i => h1 i, fun i j hij => h2 i j hij, fun i => ?_⟩
  obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
  refine step_iff.2 ⟨f, hsurj, fun g v hv => ?_, hker⟩
  have e := hint g v hv
  rw [ofChar_apply] at e
  show f (τ g v) = ofChar η g (f v)
  rw [h, map_smul, e, ofChar_apply, hη, Units.val_mul, smul_eq_mul]
  ring

theorem jhMult_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ : G →* ℂˣ} (θ : G →* ℂˣ)
    (h : ∀ g v, τ g v = (((δ g)⁻¹ : ℂˣ) : ℂ) • ρ g v) :
    jhMult (ofChar θ) τ = jhMult (ofChar (θ * δ)) ρ := by
  have key : ∀ r, OccursTimes (ofChar θ) τ r ↔ OccursTimes (ofChar (θ * δ)) ρ r := fun r =>
    ⟨occursTimes_of_twist (δ := δ)
        (fun g v => by rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])
        (fun g => MonoidHom.mul_apply θ δ g),
      occursTimes_of_twist (δ := δ⁻¹) (fun g v => by rw [MonoidHom.inv_apply]; exact h g v)
        (fun g => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_right])⟩
  simp only [jhMult, key]

private lemma pres_iterate_zero {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) (S : Subrepresentation ρ)
    (f : V →ₗ[ℂ] ℂ) (hf : ∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = ofChar θ g (f v)) (v : V)
    (hv : v ∈ S.toSubmodule) : ∃ u ∈ fixed ρ H, u ∈ S.toSubmodule ∧ f u = f v := by

  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix hρ hH v
  haveI : U.FiniteIndex := hU
  letI : Fintype (H ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  refine ⟨GlobalTheory.LocGL.idem hρ hH v, GlobalTheory.LocGL.idem_mem hρ hH v, ?_, ?_⟩
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv]
    exact S.toSubmodule.smul_mem _ (S.toSubmodule.sum_mem fun q _ => S.apply_mem_toSubmodule _ hv)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv, map_smul, map_sum]
      have hq : ∀ q : H ⧸ U, f (ρ (q.out : H) v) = f v := fun q => by
        rw [hf _ v hv, ofChar_apply, hθ _ (q.out).2, Units.val_one, one_mul]
      have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
      simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem jhMult_onFixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) :
    jhMult (ofChar θ) ρ = jhMult (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) := by
  let ι : (onFixed ρ H (MonoidHom.id G) hn).IntertwiningMap ρ :=
    { toLinearMap := (fixed ρ H).subtype
      isIntertwining' := fun g => by ext v; rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have key : ∀ r, OccursTimes (ofChar θ) ρ r ↔
      OccursTimes (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) r := by
    intro r
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      refine ⟨fun i => subComap ι (S i), fun i => subComap ι (T i), fun i => subComap_mono ι (h1 i),
        fun i j hij => subComap_mono ι (h2 i j hij), fun i => ?_⟩
      obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
      refine step_iff.2 ⟨f ∘ₗ (fixed ρ H).subtype, fun w => ?_, fun g u hu => hint g u.1 hu,
        fun u hu => hker u.1 hu⟩
      obtain ⟨v, hv, rfl⟩ := hsurj w
      obtain ⟨u, huF, huS, hfu⟩ := pres_iterate_zero hρ hH hθ (S i) f hint v hv
      exact ⟨⟨u, huF⟩, huS, hfu⟩
    · rintro ⟨S, T, h1, h2, h3⟩
      exact ⟨fun i => subMap ι (S i), fun i => subMap ι (T i), fun i => subMap_mono ι (h1 i),
        fun i j hij => subMap_mono ι (h2 i j hij),
        fun i => step_iff.2 (step_map ι hι (step_iff.1 (h3 i)))⟩
  simp only [jhMult, key]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_unitsO : IsCompact {x : kˣ | valuation k (x : k) = 1} := by
  haveI : T1Space k := IsTopologicalAddGroup.t1Space k (by
    first
      | exact isClosed_singleton
      | (convert (Valuation.isClosed_sphere (v := valuation k) 0) using 1
         ext x
         simp))
  have hS : IsCompact (((valuation k).integer.toSubmonoid : Submonoid k) : Set k) :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  convert Submonoid.units_isCompact hS using 1
  ext x
  have h0 : valuation k (x : k) ≠ 0 := by simp
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro hx
    simp [hx]
  · rintro ⟨h1, h2⟩
    rw [inv_le_one₀ (zero_lt_iff.2 h0)] at h2
    exact le_antisymm h1 h2

theorem isCompact_torusO (n : Type) : IsCompact (torusO k n : Set (n → kˣ)) :=
  isCompact_pi_infinite fun _ => isCompact_unitsO k

theorem deltaHalf_torusO {n : Type} [Fintype n] [LinearOrder n] {t : n → kˣ} (ht : t ∈ torusO k n) :
    deltaHalf k (fun _ : n => Unit) (leviTorus k n t) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hdet : Matrix.GeneralLinearGroup.det (leviTorus k n t a) = t a :=
    congrFun ((leviTorus k n).symm_apply_apply t) a
  have hv : valuation k (t a : k) = 1 := (show ∀ i, valuation k (t i : k) = 1 from ht) a
  apply Units.ext
  rw [hdet, val_absPow, nabs_eq_one k hv, Units.val_one]
  simp

variable {k} {n V : Type} [Fintype n] [DecidableEq n] [LinearOrder n] [AddCommGroup V] [Module ℂ V]

theorem jacB_apply (π : Representation ℂ (GL n k) V) (g : n → kˣ) (v : Jacquet π (unipB k n)) :
    jacB π g v = (((((deltaHalf k fun _ : n => Unit).comp
      (leviTorus k n).toMonoidHom) g)⁻¹ : ℂˣ) : ℂ) • jacBU π g v := by
  first
    | exact twist_apply (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v
    | (show twist (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v = _
       rw [twist_apply]
       rfl)

theorem jhMult_jacBU_eq_expMult {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π)
    {θ : (n → kˣ) →* ℂˣ} (hθ : ∀ t ∈ torusO k n, θ t = 1) :
    jhMult (ofChar θ) (jacBU π) = expMult π θ := by
  unfold expMult jacBUFixed
  exact jhMult_onFixed (isSmooth_jacBU hπ) (isCompact_torusO k n) _ hθ

theorem jhMult_jacB_eq_expMult : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  intro k _ _ _ _ n V _ _ π hπ θ hθ
  rw [jhMult_of_twist θ (fun g v => jacB_apply π g v)]
  refine jhMult_jacBU_eq_expMult hπ fun t ht => ?_
  rw [MonoidHom.mul_apply, hθ t ht, one_mul]
  exact deltaHalf_torusO k ht

end GlobalTheory.SmGL.UnramFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTwistsByLevelCharacter
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowClassSum

section Generic

open Formalism.IndefR.Bridge

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}

theorem card_stab (γ : Γ) (h : G) (k : J) :
    Nat.card (stab ι J (ι γ * h * k)) = Nat.card (stab ι J h) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  have e : (ι γ * h * k)⁻¹ * ι δ * (ι γ * h * k) =
      (k : G)⁻¹ * (h⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * h) * k := by
    simp [mul_assoc]
  rw [mem_stab, mem_stab, e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInner_indep (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y y' : I → G} (hy : IsReps ι J y) (hy' : IsReps ι J y')
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y' F F' = adInner ι J y F F' := by
  choose s γ k hs using fun i => (hy (y' i)).exists
  have hinj : Function.Injective s := by
    intro i j hij
    refine (hy' (y' i)).unique ⟨1, 1, by simp⟩ ⟨γ i * (γ j)⁻¹, (k j)⁻¹ * k i, ?_⟩
    rw [hs i, hs j, hij]
    simp [mul_assoc]
  unfold adInner
  refine Fintype.sum_bijective s (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hs i, card_stab, hF, hF', inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ, hρ]
  simp

variable {Q : Subgroup G} {ch : Q →* ℂˣ}

theorem reductionGroupAction_mem_adelicForms (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    (κ : Q) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) : g0Act ch κ F ∈ AdForms ι ρ J χ := by
  intro γ h k
  have hk := hn κ κ.2 k k.2
  have e : ι γ * h * k * κ = ι γ * (h * κ) * ((⟨_, hk⟩ : J) : G) := by simp [mul_assoc]
  have e2 : χ ⟨_, hk⟩ = χ k := by
    rw [← hch, ← hch]
    have : (⟨_, hJ hk⟩ : Q) = κ⁻¹ * ⟨k, hJ k.2⟩ * κ := rfl
    rw [this, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  unfold g0Act
  rw [e, hF, e2, map_smul, smul_comm]

theorem adInner_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (κ : Q) (hκ : ‖(ch κ : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y)
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y (g0Act ch κ F) (g0Act ch κ F') = adInner ι J y F F' := by
  have hn' : ∀ k ∈ J, (κ : G) * k * (κ : G)⁻¹ ∈ J := fun k hk => by
    simpa using hn _ (Q.inv_mem κ.2) k hk
  have hy' : IsReps ι J fun i => y i * κ := by
    intro h
    refine (existsUnique_congr fun i => ?_).1 (hy (h * (κ : G)⁻¹))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn κ κ.2 k k.2⟩, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at e
      rw [e]; simp [mul_assoc]
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn' k k.2⟩, ?_⟩
      rw [e]; simp [mul_assoc]
  rw [← adInner_indep hρ hχ hy hy' hF hF']
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : stab ι J (y i * κ) = stab ι J (y i) := by
    ext δ
    rw [mem_stab, mem_stab]
    constructor
    · intro h
      simpa [mul_assoc] using hn' _ h
    · intro h
      simpa [mul_assoc] using hn κ κ.2 _ h
  rw [hs, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), Complex.conj_mul',
    Units.val_inv_eq_inv_val, norm_inv, hκ]
  simp

theorem exists_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hn1 : ∀ q, ‖(ch q : ℂ)‖ = 1)
    (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y) (M : Links.HMod (G → W))
    (hM : M.Is (AdForms ι ρ J χ) (adInner ι J y)) (κ : Q) (x : M.H) :
    ∃ x' : M.H, M.e x' = g0Act ch κ (M.e x) ∧ ‖x'‖ = ‖x‖ := by
  obtain ⟨-, hr, hi⟩ := hM
  have hχ : ∀ k, ‖(χ k : ℂ)‖ = 1 := fun k => by
    rw [← hch]; exact hn1 _
  have hx : M.e x ∈ AdForms ι ρ J χ := by
    rw [← hr]; exact ⟨x, rfl⟩
  have hm := reductionGroupAction_mem_adelicForms hJ hn hch κ hx
  rw [← hr] at hm
  obtain ⟨x', hx'⟩ := hm
  refine ⟨x', hx', ?_⟩
  have e : inner ℂ x' x' = inner ℂ x x := by
    rw [hi, hi, hx']
    exact adInner_g0Act hρ hχ hn κ (hn1 _) hy hx hx
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, e]

theorem twistedTranslate_apply_eq_inv_smul {a : G} (ha : a ∈ Q) (F : G → W) (h : G) {z : ℂ} (hz : ((ch ⟨a, ha⟩ : ℂˣ) : ℂ) = z) :
    g0Act ch ⟨a, ha⟩ F h = z⁻¹ • F (h * a) := by
  rw [← hz, ← Units.val_inv_eq_inv_val]
  rfl

end Generic

variable {D : D7}

theorem norm_levFn_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (flagL L).P.H (flagL L).P.chi (Formalism.L2.DIV.rTup β (flagL L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

theorem conj_mem_flag1L (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {a b : GL (Fin V.rank) (Lev.EAf D)} (ha : a ∈ lev D.sp.cm V.gram β (flagL L))
    (hb : b ∈ lev D.sp.cm V.gram β (flag1L L)) : a⁻¹ * b * a ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have h1 : a ∈ parLev D.sp.cm V.gram β L := ha.1
  have h2 : b ∈ parLev D.sp.cm V.gram β L := hb.1
  have h3 : rTup β L b = 1 := Subgroup.mem_bot.1 hb.2
  have h4 : a⁻¹ * b ∈ parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
  have h5 : rTup β L (a⁻¹ * b * a) = 1 := by
    rw [rTup_mul h4 h1, rTup_mul (Subgroup.inv_mem _ h1) h2, rTup_inv h1, h3, mul_one, inv_mul_cancel]
  exact ⟨Subgroup.mul_mem _ h4 h1, Subgroup.mem_bot.2 h5⟩

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ κ ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, κ⁻¹ * k * κ ∈ (levEnv V β L).J := by
  intro κ hκ k hk
  have h := conj_mem_flag1L V β L (a := Formalism.UG.bc (swapAE D) κ.1) (b := Formalism.UG.bc (swapAE D) k.1) hκ hk
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem levEnv_ch (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem mem_levEnv_Q {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g0 : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g0 κ) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := by
  have h : finE V κ ∈ lev D.sp.cm V.gram β (flagL L) := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact h

theorem levEnv_ch_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) = levChi V β (flagL L) κ := by
  rw [levEnv_ch]
  rfl

theorem exists_translate (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (c : CoefA V) (hc : c.Is) (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq := mem_levEnv_Q hκ
  have hch : ∀ q, ‖(((levEnv V β L).ch q : ℂˣ) : ℂ)‖ = 1 := fun q => by
    rw [levEnv_ch]; exact norm_levFn_flagL V β L _
  have hρ : ∀ (γ : GQ V) (u u' : c.W),
      inner ℂ ((c.ρ.comp (GQ V).subtype) γ u) ((c.ρ.comp (GQ V).subtype) γ u') = inner ℂ u u' :=
    fun γ u u' => hc.2.1 γ.1 u u'
  have key : ∃ x' : M.H, M.e x' = Bridge.g0Act (levEnv V β L).ch ⟨_, hq⟩ (M.e x) ∧ ‖x'‖ = ‖x‖ :=
    exists_g0Act (W := c.coef.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (χ := (levEnv V β L).χ)
      (ch := (levEnv V β L).ch) hρ hch (levEnv V β L).J_le (levEnv_normal V β L) (levEnv V β L).ch_J hy M hM ⟨_, hq⟩ x
  obtain ⟨x', hx', hn⟩ := key
  refine ⟨x', fun h => ?_, hn⟩
  refine Eq.trans ?_ (twistedTranslate_apply_eq_inv_smul (ch := (levEnv V β L).ch) hq (M.e x) h (levEnv_ch_lift hq))
  exact congrFun hx' h

end GlobalTheory.RowClassSum

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeIndexAdditive
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.SumSig

section Change
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem gram_family (S : HSpace E) {ι : Type} [Fintype ι] (v : ι → S.V) :
    (Matrix.of fun k l => S.hT (v k) (v l)) =
      (Matrix.of fun i k => S.frame.repr (v k) i)ᴴ * S.gram * Matrix.of fun i k => S.frame.repr (v k) i := by
  ext k l
  have hk := S.frame.sum_repr (v k)
  have hl := S.frame.sum_repr (v l)
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram]
  conv_lhs => rw [← hk, ← hl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    Finset.sum_mul, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Change

end GlobalTheory.SumSig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
open GlobalTheory.Doubling GlobalTheory.AdelicU

namespace GlobalTheory.Twist.OrthSum

variable {D : D7}

theorem pair_hsum (V W : HSp D) (x y : Fin (hsum V W).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (hsum V W).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * V.gram i j * y (finSumFinEquiv (Sum.inl j))) +
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * W.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hsum]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Doubling.blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

theorem selfDual_hsum {V W : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') :
    IsSelfDualC (hsum V W) (sumLat finSumFinEquiv L L') := by
  have hsumLat : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L') := by
    let φ : ((Fin V.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (V.rank + W.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L' =
        (L.prod L').map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL'.1.fg).map _)
  refine ⟨hsumLat, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL'.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ + b₂, ?_⟩
    rw [pair_hsum]
    push_cast
    linear_combination hb₁ + hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL'.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero] at hb
      exact ⟨b, hb⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add] at hb
      exact ⟨b, hb⟩

end GlobalTheory.Twist.OrthSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
section
noncomputable section

namespace GlobalTheory.GaussLine

open Complex NumberField

def heisFun {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p)

def dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : V → ℂ)
    (x : V) : ℂ :=
  fderiv ℝ f x w.1 - 2 * Real.pi * Complex.I * (β x w.2 : ℂ) * f x

variable (F : Type) [Field F] [NumberField F]

def pairInf (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [smul_mul_assoc, ← Finset.smul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [mul_smul_comm, ← Finset.smul_sum])

theorem pairInf_apply (κ : Type) [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    pairInf F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

theorem heisFun_apply {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) (x : V) :
    heisFun β p q f x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p) := rfl

end GlobalTheory.GaussLine

end
end

