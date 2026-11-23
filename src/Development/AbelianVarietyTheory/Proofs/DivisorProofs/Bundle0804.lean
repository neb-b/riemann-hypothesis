module

public import Mathlib
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatEnt

def QSum {G : Type} [CommGroup G] (H : Subgroup G) (F : G → ℂ) (a : ℂ) : Prop :=
  HasSum (fun q : G ⧸ H => F q.out) a

section Generic

variable {G : Type} [CommGroup G] {H H' : Subgroup G} {F : G → ℂ} {a : ℂ}

theorem out_mk (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (g : G) : F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hu, hF _ _ u.2]

theorem QSum.translate (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) (t : G) :
    QSum H (fun g => F (t * g)) a := by
  unfold QSum at *
  rw [← (Equiv.mulLeft (QuotientGroup.mk t : G ⧸ H)).hasSum_iff] at h
  refine h.congr_fun fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : ∀ g, ∀ u ∈ H, F (t * (g * u)) = F (t * g) := fun g u hu => by rw [← mul_assoc, hF _ _ hu]
  exact (out_mk (F := fun g => F (t * g)) h2 g).trans (out_mk hF (t * g)).symm

theorem QSum.eq_zero (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) {t : G} {c : ℂ} (hc : c ≠ 1)
    (ht : ∀ g, F (t * g) = c * F g) : a = 0 := by
  have h1 := h.translate hF t
  unfold QSum at *
  simp only [ht] at h1
  have h2 := h1.unique (h.mul_left c)
  have : (c - 1) * a = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem qsum_index (hle : H ≤ H') (hn : H.relIndex H' ≠ 0) (hF : ∀ g, ∀ u ∈ H', F (g * u) = F g) :
    QSum H' F a ↔ QSum H F (H.relIndex H' * a) := by
  unfold QSum
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hn⟩
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  have hc : (Fintype.card (H' ⧸ H.subgroupOf H') : ℂ) = H.relIndex H' := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hn' : (H.relIndex H' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  let e := Subgroup.quotientEquivProdOfLE hle
  have he : ∀ q : G ⧸ H, F q.out = (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q) := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [out_mk fun g u hu => hF g u (hle hu)]
    show _ = F (QuotientGroup.mk g : G ⧸ H').out * 1
    rw [out_mk hF, mul_one]
  simp only [he]
  rw [show (fun q => (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q)) =
    (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) ∘ e from rfl, e.hasSum_iff]
  have h1 : HasSum (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) (H.relIndex H') := by
    simpa [hc] using hasSum_fintype (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ))
  constructor
  · intro h
    rw [mul_comm]
    have h3 := summable_mul_of_summable_norm (f := fun q : G ⧸ H' => F q.out)
      (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h.summable.norm h1.summable.norm
    exact HasSum.mul (f := fun q : G ⧸ H' => F q.out) (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h h1 h3
  · intro h
    have h2 := (h.prod_fiberwise fun q => h1.mul_left (F q.out)).mul_right (H.relIndex H' : ℂ)⁻¹
    simp only [mul_assoc, mul_inv_cancel₀ hn', mul_one] at h2
    rwa [mul_left_comm, mul_inv_cancel₀ hn', mul_one] at h2

end Generic

variable {E : Type} [Field E] [NumberField E]

def box (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Set (Af E)ˣ :=
  {z | ∀ w, Valued.v ((z : Af E) w - 1) ≤ r w}

def congr (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Subgroup (Af E)ˣ where
  carrier := {z | ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w}
  one_mem' := fun w => by
    have : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl
    rw [this]; simp
  mul_mem' := fun {a b} ha hb w => by
    have : ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl
    rw [this]
    refine ⟨by rw [map_mul, (ha w).1, (hb w).1, one_mul], ?_⟩
    rw [show (a : Af E) w * (b : Af E) w - 1 = (a : Af E) w * ((b : Af E) w - 1) + ((a : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (ha w).1, one_mul]; exact (hb w).2) (ha w).2
  inv_mem' := fun {a} ha w => by
    have h : (a : Af E) w * ((a⁻¹ : (Af E)ˣ) : Af E) w = 1 := (coord w a).val_inv
    have h1 : Valued.v (((a⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by
      have := congrArg Valued.v h
      rwa [map_mul, (ha w).1, one_mul, map_one] at this
    refine ⟨h1, ?_⟩
    rw [show ((a⁻¹ : (Af E)ˣ) : Af E) w - 1 = -(((a⁻¹ : (Af E)ˣ) : Af E) w * ((a : Af E) w - 1)) by
      linear_combination h, Valuation.map_neg, map_mul, h1, one_mul]
    exact (ha w).2

def radN (E : Type) [Field E] [NumberField E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : WithZero (Multiplicative ℤ) :=
  Valued.v (N : w.adicCompletion E)

def zterm (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : ℂ := (finPart χ z : ℂ) * ((modF z : ℝ) : ℂ) ^ s

theorem zterm_mul (χ : HChar E) (s : ℂ) (z z' : (Af E)ˣ) : zterm χ s (z * z') = zterm χ s z * zterm χ s z' := by
  unfold zterm
  rw [map_mul, ObjModel.modF_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ObjModel.modF_pos _).le (ObjModel.modF_pos _).le, Units.val_mul]
  ring

theorem differentiable_zterm (χ : HChar E) (z : (Af E)ˣ) : Differentiable ℂ fun s => zterm χ s z :=
  Differentiable.const_mul (Differentiable.const_cpow differentiable_id
    (Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))) _

theorem modF_eq_one {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) : modF u = 1 := by
  unfold modF
  exact finprod_eq_one_of_forall_eq_one fun v => by simp [hu v]

theorem zterm_unit (χ : HChar E) (s : ℂ) {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) :
    zterm χ s u = finPart χ u := by
  simp [zterm, modF_eq_one hu]

theorem norm_zterm {χ : HChar E} (h : IsUnitary χ) (s : ℂ) (z : (Af E)ˣ) : ‖zterm χ s z‖ = modF z ^ s.re := by
  have : ‖(finPart χ z : ℂ)‖ = 1 := h _
  rw [zterm, norm_mul, this, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ObjModel.modF_pos z)]

theorem mul_mem_box {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z u : (Af E)ˣ} (hu : u ∈ congr r) :
    z * u ∈ box r ↔ z ∈ box r := by
  have key : ∀ z u : (Af E)ˣ, u ∈ congr r → z ∈ box r → z * u ∈ box r := fun z u hu hz w => by
    have : ((z * u : (Af E)ˣ) : Af E) w = (z : Af E) w * (u : Af E) w := rfl
    rw [this, show (z : Af E) w * (u : Af E) w - 1 = (u : Af E) w * ((z : Af E) w - 1) + ((u : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (hu w).1, one_mul]; exact hz w) (hu w).2
  exact ⟨fun h => by simpa using key _ _ (inv_mem hu) h, key _ _ hu⟩

theorem congr_mono {r r' : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} (h : ∀ w, r w ≤ r' w) :
    congr r ≤ congr r' := fun _ hz w => ⟨(hz w).1, (hz w).2.trans (h w)⟩

theorem mem_hatO_of_sub {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) {a z : Af E} (ha : a ∈ hatO c)
    (hz : ∀ P, Valued.v (z P - a P) ≤ radN E n P) : z ∈ hatO c := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key := GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by
      show _ ∈ hatO c
      rw [← map_mul]
      refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)
      simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) fun P => by
      have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hn
      show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - a P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
  have e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) + a := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]
  rw [e]
  exact add_mem key ha

theorem congr_le_hatOUnits {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) :
    congr (radN E n) ≤ hatOUnits c := fun _ hu =>
  mem_hatOUnits.2 ⟨mem_hatO_of_sub hn hc (one_mem _) fun P => (hu P).2,
    mem_hatO_of_sub hn hc (one_mem _) fun P => (inv_mem hu P).2⟩

theorem hatOUnits_le_congr (c : Ideal (OF E)) : hatOUnits c ≤ congr (fun _ => 1) := fun u hu w => by
  have h : Valued.v ((u : Af E) w) = 1 :=
    GlobalTheory.Mem.TupHecke.valued_eq_one_of_le (coord w u) (ObjModel.hatO_integral hu.1 w) (ObjModel.hatO_integral hu.2 w)
  exact ⟨h, Valuation.map_sub_le _ h.le (by simp)⟩

end GlobalTheory.CMVal.LatEnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExtProj

open Matrix

variable {W : Type} [CommRing W] {n : ℕ} {R' : Type} [CommRing R'] (β : W →+* R') (v : Fin n → R')

theorem act_one : ((1 : Matrix (Fin n) (Fin n) W).map β) *ᵥ v = (1 : R') • v := by
  rw [Matrix.map_one _ (map_zero β) (map_one β), one_mulVec, one_smul]

theorem act_add {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M + N).map β) *ᵥ v = (s + s') • v := by
  rw [Matrix.map_add _ (map_add β), add_mulVec, hM, hN, add_smul]

theorem act_sub {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M - N).map β) *ᵥ v = (s - s') • v := by
  rw [Matrix.map_sub _ (map_sub β), sub_mulVec, hM, hN, sub_smul]

theorem act_smul {M : Matrix (Fin n) (Fin n) W} {s : R'} (r : W) (hM : (M.map β) *ᵥ v = s • v) :
    ((r • M).map β) *ᵥ v = (β r * s) • v := by
  have : (r • M).map β = β r • M.map β := by ext; simp
  rw [this, Matrix.smul_mulVec, hM, smul_smul]

theorem act_mul {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M * N).map β) *ᵥ v = (s * s') • v := by
  rw [Matrix.map_mul, ← mulVec_mulVec, hN, mulVec_smul, hM, smul_smul, mul_comm]

theorem act_list {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (l : List κ) :
    (((l.map F).prod).map β) *ᵥ v = (l.map S).prod • v := by
  induction l with
  | nil => simpa using act_one β v
  | cons j l ih => simpa using act_mul β v (h j) ih

theorem act_finset {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (s : Finset κ) :
    ((∑ j ∈ s, F j).map β) *ᵥ v = (∑ j ∈ s, S j) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj]; exact act_add β v (h j) ih

theorem act_finsupp {O : Type} (F : O → Matrix (Fin n) (Fin n) W) (S : O → R')
    (h : ∀ x, ((F x).map β) *ᵥ v = S x • v) (f : O →₀ W) :
    ((f.sum fun x r => r • F x).map β) *ᵥ v = (f.sum fun x r => β r * S x) • v :=
  act_finset β v _ _ (fun x => act_smul β v (f x) (h x)) f.support

theorem ext_mulVec {L : Type} [Field L] {M N : Matrix (Fin n) (Fin n) L} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

end GlobalTheory.LieExtProj

namespace GlobalTheory.LieExtProj
open Matrix

theorem rhoPart_splits_by_idempotents : ∀ (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (O : Type) [CommRing O] (n a : ℕ) (A : O →+* Matrix (Fin n) (Fin n) W) (ω : O) (tr nm : ℤ) (ρ : W) (t : Fin a → (O →+* W)), ω ^ 2 - tr * ω + nm = 0 → ρ ^ 2 - tr * ρ + nm = 0 → (∀ i, t i ω = ρ) → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((tr ^ 2 - 4 * nm : ℤ) : W) → (∀ v : Fin n → L, ((A ω).map (algebraMap W L)).mulVec v = algebraMap W L ρ • v → ∃ w : Fin a → Fin n → L, (∀ i c, ((A c).map (algebraMap W L)).mulVec (w i) = algebraMap W L (t i c) • w i) ∧ v = ∑ i, w i) → ∃ Q : Fin a → Matrix (Fin n) (Fin n) W, (∀ i, Q i * Q i = Q i) ∧ (∀ i c, A c * Q i = t i c • Q i) ∧ (∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β).mulVec v = β ρ • v → v = ∑ i, ((Q i).map β).mulVec v) ∧ ∀ (R' : Type) [CommRing R'] (β : W →+* R') (i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β).mulVec v = β (t i c) • v) → ((Q i).map β).mulVec v = v := by
  intro W L _ _ _ _ _ O _ n a A ω tr nm ρ t hω hρ htω hcop hdisc hsplit
  classical
  have hu2 : (2 * ρ - tr) * (2 * ρ - tr) = ((tr ^ 2 - 4 * nm : ℤ) : W) := by
    push_cast; linear_combination 4 * hρ
  have hu : IsUnit (2 * ρ - (tr : W)) := isUnit_of_mul_isUnit_left (hu2 ▸ hdisc)
  obtain ⟨ui, hui⟩ := hu.exists_left_inv
  set P : Matrix (Fin n) (Fin n) W := ui • (A ω + (ρ - tr) • 1) with hPdef

  have hf : ∀ i j, ∃ f : O →₀ W, i ≠ j →
      (f.sum fun x r => r * t i x) - (f.sum fun x r => r * t j x) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : W) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hcop i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      refine ⟨f, fun _ => ?_⟩
      rw [← hf, ← Finsupp.sum_sub]
      simp [Finsupp.sum, smul_eq_mul, mul_sub]
  choose f hf using hf
  let Z : Fin a → Fin a → Matrix (Fin n) (Fin n) W := fun i j =>
    ((f i j).sum fun x r => r • A x) - ((f i j).sum fun x r => r * t j x) • (1 : Matrix (Fin n) (Fin n) W)
  let E : Fin a → Matrix (Fin n) (Fin n) W := fun i =>
    ((List.finRange a).map fun j => if j = i then 1 else Z i j).prod
  let Q : Fin a → Matrix (Fin n) (Fin n) W := fun i => E i * P

  have hP : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'),
      ((A ω).map β) *ᵥ v = β ρ • v → (P.map β) *ᵥ v = v := by
    intro R' _ β v hv
    have h := act_smul β v ui (act_add β v hv (act_smul β v (ρ - tr) (act_one β v)))
    rw [h]
    have : β ui * (β ρ + β (ρ - tr) * 1) = β (ui * (2 * ρ - tr)) := by
      simp only [map_mul, map_sub, map_ofNat, _root_.mul_one]; ring
    rw [this, hui, map_one, one_smul]

  have hE : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((E i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have hZ : ∀ j, ((if j = i then 1 else Z i j).map β) *ᵥ v =
        (if j = i then 1 else β ((f i j).sum fun x r => r * t k x) - β ((f i j).sum fun x r => r * t j x)) • v := by
      intro j
      split_ifs
      · exact act_one β v
      · have h1 := act_finsupp β v (fun x => A x) (fun x => β (t k x)) hv (f i j)
        have h2 := act_sub β v h1 (act_smul β v ((f i j).sum fun x r => r * t j x) (act_one β v))
        refine h2.trans ?_
        congr 1
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Finsupp.sum, map_sum, map_mul]
    rw [act_list β v _ _ hZ]
    by_cases hki : k = i
    · rw [if_pos hki]
      subst hki
      refine congrArg (· • v) ?_
      apply List.prod_eq_one
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      split_ifs with hj
      · rfl
      · rw [← map_sub, hf k j (Ne.symm hj), map_one]
    · rw [if_neg hki]
      refine congrArg (· • v) ?_
      apply List.prod_eq_zero
      refine List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩
      rw [if_neg hki, sub_self]
  have hQ : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((Q i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have h1 : (P.map β) *ᵥ v = (1 : R') • v := by
      rw [one_smul]; exact hP R' β v (by rw [hv, htω])
    have h2 := hE R' β k i v hv
    have h3 := act_mul β v h2 h1
    rw [_root_.mul_one] at h3
    exact h3

  have hAP : A ω * P = ρ • P := by
    have hω' : ω * ω = (tr : O) * ω - (nm : O) := by linear_combination hω
    have hA2 : A ω * A ω = (tr : W) • A ω - (nm : W) • (1 : Matrix (Fin n) (Fin n) W) := by
      rw [← map_mul, hω', map_sub, map_mul, map_intCast, map_intCast]
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, zsmul_one, ← zsmul_eq_mul]
    have hnm : (nm : W) = tr * ρ - ρ ^ 2 := by linear_combination hρ
    rw [hPdef, mul_smul_comm, mul_add, mul_smul_comm, _root_.mul_one, hA2, hnm]
    module

  set βL := algebraMap W L
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) W => M.map βL :=
    Matrix.map_injective (IsFractionRing.injective W L)
  have hdec : ∀ x : Fin n → L, ∃ w : Fin a → Fin n → L,
      (∀ i, ((Q i).map βL) *ᵥ x = w i) ∧ (∀ i c, ((A c).map βL) *ᵥ w i = βL (t i c) • w i) ∧
      (P.map βL) *ᵥ x = ∑ i, w i := by
    intro x
    have hy : ((A ω).map βL) *ᵥ ((P.map βL) *ᵥ x) = βL ρ • ((P.map βL) *ᵥ x) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, hAP]
      have : (ρ • P).map βL = βL ρ • P.map βL := by ext; simp
      rw [this, Matrix.smul_mulVec]
    obtain ⟨w, hw, hsum⟩ := hsplit _ hy
    refine ⟨w, fun i => ?_, hw, hsum⟩
    show ((E i * P).map βL) *ᵥ x = w i
    rw [Matrix.map_mul, ← mulVec_mulVec, hsum, mulVec_sum]
    rw [Finset.sum_eq_single i]
    · rw [hE L βL i i (w i) (hw i), if_pos rfl, one_smul]
    · intro k _ hk; rw [hE L βL k i (w k) (hw k), if_neg hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  choose w hwQ hwA hwP using hdec
  have hsumQ : ∑ i, Q i = P := by
    apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [hwP x]
    have : (∑ i, Q i).map βL = ∑ i, (Q i).map βL := by ext; simp [Matrix.sum_apply]
    rw [this, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun i _ => hwQ x i
  refine ⟨Q, fun i => ?_, fun i c => ?_, ?_, ?_⟩
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hQ L βL i i _ (hwA x i), if_pos rfl, one_smul]
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    have : (t i c • Q i).map βL = βL (t i c) • (Q i).map βL := by ext; simp
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hwA x i c, this, Matrix.smul_mulVec, hwQ x i]
  · intro R' _ β v hv
    have : (∑ i, Q i).map β = ∑ i, (Q i).map β := by ext; simp [Matrix.sum_apply]
    rw [← Matrix.sum_mulVec, ← this, hsumQ, hP R' β v hv]
  · intro R' _ β i v hv
    rw [hQ R' β i i v hv, if_pos rfl, one_smul]

end GlobalTheory.LieExtProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqToUnitCompOfConstOnFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FibreConstTorus

theorem toUnit_left {S : Scheme.{0}} (G : Over S) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (f ≫ g).appTop a = f.appTop (g.appTop a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

end FibreConstTorus


open FibreConstTorus in
theorem eq_toUnit_comp_of_const_on_fibres : ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj B], IsAbelianScheme B → ∀ q : G ⟶ B, Flat q.left → Surjective q.left → QuasiCompact q.left → ∀ (X : Type) [AddCommGroup X] (d : G ⟶ splitTorus S X), (∀ (Z : Over S) (x y : Z ⟶ G), x ≫ q = y ≫ q → x ≫ d = y ≫ d) → ∃ a : 𝟙_ (Over S) ⟶ splitTorus S X, d = toUnit G ≫ a := by
  intro S G B _ hB q hfl hsu hqc X _ d hd
  have hE : EffectiveEpi q.left := inferInstance
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  have hbij : Function.Bijective B.hom.appTop.hom := globalFns_holds S B hB

  have hpb := IsPullback.of_hasPullback q.left q.left
  let Z : Over S := Over.mk (pullback.fst q.left q.left ≫ G.hom)
  let x : Z ⟶ G := Over.homMk (pullback.fst q.left q.left) rfl
  let y : Z ⟶ G := Over.homMk (pullback.snd q.left q.left) (by
    change pullback.snd q.left q.left ≫ G.hom = pullback.fst q.left q.left ≫ G.hom
    rw [← hq, pullback.condition_assoc])
  have hxy : x ≫ q = y ≫ q := by
    ext1
    exact (pullback.condition (f := q.left) (g := q.left))
  have hdl : pullback.fst q.left q.left ≫ d.left = pullback.snd q.left q.left ≫ d.left :=
    congrArg CommaMorphism.left (hd Z x y hxy)
  have key : ∀ c : Γ((splitTorus S X).left, ⊤),
      (pullback.fst q.left q.left).appTop (d.left.appTop c) =
        (pullback.snd q.left q.left).appTop (d.left.appTop c) := fun c => by
    rw [← appTop_comp_apply, ← appTop_comp_apply, hdl]

  obtain ⟨f, hf⟩ : ∃ f, f = splitTorusPointsEquiv S X G d := ⟨_, rfl⟩
  have hfv : ∀ χ : X, (f (Multiplicative.ofAdd χ)).val = d.left.appTop (charUnit S X χ).val :=
    fun χ => hf ▸ splitTorusPointsEquiv_val S X G d χ
  let incl : Γ(S, ⊤)ˣ →* Γ(G.left, ⊤)ˣ := Units.map G.hom.appTop.hom.toMonoidHom
  have hinclv : ∀ u, (incl u).val = G.hom.appTop u.val := fun u => rfl
  have hinj : Function.Injective incl := by
    intro u u' h
    apply Units.ext
    apply hbij.1
    apply FlatDescent.injective_appTop_of_epi q.left
    have h' := congrArg Units.val h
    rw [hinclv, hinclv, ← hq, appTop_comp_apply, appTop_comp_apply] at h'
    exact h'
  have hrange : ∀ m, f m ∈ incl.range := by
    intro m
    obtain ⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m := ⟨Multiplicative.toAdd m, rfl⟩
    obtain ⟨v, hv, -⟩ := (FlatDescent.existsUnique_units_appTop_eq_iff q.left hpb
      (f (Multiplicative.ofAdd χ))).2 (by
        apply Units.ext
        rw [Units.coe_map, Units.coe_map]
        change (pullback.fst q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val =
          (pullback.snd q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val
        rw [hfv]
        exact key _)
    let e := RingEquiv.ofBijective B.hom.appTop.hom hbij
    refine ⟨Units.map e.symm.toMonoidHom v, Units.ext ?_⟩
    rw [← hv, hinclv]
    change G.hom.appTop (e.symm v.val) = q.left.appTop v.val
    rw [← hq, appTop_comp_apply]
    congr 1
    exact e.apply_symm_apply v.val
  let φ : Multiplicative X →* Γ(S, ⊤)ˣ :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (f.codRestrict incl.range hrange)
  have hφ : ∀ m, incl (φ m) = f m := by
    intro m
    have h2 := MonoidHom.ofInjective_apply hinj (x := (MonoidHom.ofInjective hinj).symm ⟨f m, hrange m⟩)
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  refine ⟨(splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ, ?_⟩
  apply (splitTorusPointsEquiv S X G).injective
  refine MonoidHom.ext fun m => Units.ext ?_
  obtain ⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m := ⟨Multiplicative.toAdd m, rfl⟩
  have h3 := splitTorusPointsEquiv_val S X (𝟙_ (Over S))
    ((splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ) χ
  rw [MulEquiv.apply_symm_apply] at h3
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, toUnit_left,
    appTop_comp_apply, ← h3, ← hinclv, hφ, hfv]

end GlobalTheory
end

