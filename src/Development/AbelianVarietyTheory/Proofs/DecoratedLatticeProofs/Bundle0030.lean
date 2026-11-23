module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Formalism.LocalRingCardinality.DataForms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqZeroOfFlatMapColumnZero
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat

theorem integral_pi_subtype_iff {k α : Type} [MeasurableSpace k] {P Q : α → Prop} {i1 : Fintype (Subtype P)}
    {i2 : Fintype (Subtype Q)} (h : ∀ a, P a ↔ Q a) (ν : Measure k) (F : (Subtype P → k) → ℂ)
    (G : (Subtype Q → k) → ℂ) (hFG : ∀ a, F a = G (fun e => a ⟨e.1, (h e.1).2 e.2⟩)) :
    ∫ a, F a ∂(Measure.pi fun _ => ν) = ∫ e, G e ∂(Measure.pi fun _ => ν) := by
  obtain rfl : P = Q := funext fun a => propext (h a)
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  obtain rfl : F = G := funext hFG
  rfl

def readPart {k : Type} {n n' : Type} {c : ℕ} (ρ : ℕ) (h : ρ < c + 1)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix n (n' ⊕ Unit) k :=
  Matrix.of fun r q => Sum.elim (fun s => t (.inl r) (.inl s)) (fun _ => t (.inl r) (.inr ⟨ρ, h⟩)) q

section
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_itFree (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : e ∈ itFree n n' c ρ ↔ Free (ρ + 1) e := by
  simp [itFree]

theorem mem_evAll (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ evAll n n' c ρ ↔ ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e := by
  simp [evAll]

variable {k : Type} [Field k]

theorem fill_eq (ρ : ℕ) (h : ρ < c + 1) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (a : {e // e ∈ itFree n n' c ρ} → k) :
    fill (evAll n n' c ρ) (itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) t a =
      affPt (ρ + 1) (readPart ρ h t).toCols₁ (fun e => a ⟨e.1, (mem_itFree ρ e.1).2 e.2⟩) +
        colAt n' c (ρ + 1) (fun r => readPart ρ h t r (Sum.inr ())) := by
  ext r q
  simp only [fill, affPt, Matrix.of_apply, Matrix.add_apply]
  by_cases hF : Free (ρ + 1) (r, q)
  · rw [dite_eq_left ((mem_itFree ρ _).2 hF), dite_eq_left hF]
    rcases r with r | l <;> rcases q with s | i
    · exact hF.elim
    · have h1 : ρ + 1 < i.val + 1 := hF
      have h2 : i.val ≠ ρ := by omega
      simp [basePt, colAt, h2]
    · simp [basePt, colAt]
    · have h1 : l.val < i.val := hF
      have h2 : l.val ≠ i.val := by omega
      simp [basePt, colAt, h2]
  · rw [dite_eq_right (fun hh => hF ((mem_itFree ρ _).1 hh)), dite_eq_right hF]
    by_cases hR : IsRead n n' c ρ (r, q)
    · rw [if_neg (fun hh => ((mem_evAll ρ _).1 hh).2 hR)]
      rcases r with r | l <;> rcases q with s | i
      · simp [basePt, colAt, readPart]
      · have h1 : i.val = ρ := hR
        obtain rfl : i = ⟨ρ, h⟩ := Fin.ext h1
        simp [basePt, colAt, readPart]
      · exact hR.elim
      · exact hR.elim
    · rw [if_pos ((mem_evAll ρ _).2 ⟨hF, hR⟩)]
      rcases r with r | l <;> rcases q with s | i
      · exact (hR trivial).elim
      · have h1 : i.val ≠ ρ := hR
        simp [basePt, colAt, h1]
      · simp [basePt, colAt]
      · simp [basePt, colAt]

theorem ch_add_colAt (p : ℕ) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : n → k) :
    ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end

theorem red_eq_zero_of_flCol : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  intro k _ _ _ _ _ _ ψ ν n n' _ _ _ _ c ρ hc Φ hΦ t
  have h : ρ < c + 1 := by omega
  rw [← hΦ (readPart ρ h t)]
  unfold red flCol opE
  refine integral_pi_subtype_iff (mem_itFree ρ) ν _ _ fun a => ?_
  beta_reduce
  rw [fill_eq ρ h t a, ch_add_colAt, mul_comm]

end GlobalTheory.FlatRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEvaluateEntryOfMulLaw
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology

noncomputable section
namespace GlobalTheory.PartRedEval
open GlobalTheory.PartRed

section Alg
variable {k : Type} [Field k] {R Q : Type} [DecidableEq R] [DecidableEq Q]

theorem fillAt_apply_of_notMem (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  simp [fillAt, hE, hI]

theorem fillAt_add_single (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (u : k) (y : I → k) :
    fillAt β E I (x + Matrix.single e.1 e.2 u) y = fillAt β E I x y + Matrix.single e.1 e.2 u := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 u r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    simp [fillAt, h0]

theorem fillAt_insert (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) :
    fillAt β (insert e E) I x y = fillAt β E I (x + Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2)) y := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2) r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    have h1 : (r, q) ≠ e := fun h' => h h'.symm
    simp [fillAt, h0, h1]

end Alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

theorem continuous_form (w : Matrix R Q k →ₗ[k] k) : Continuous w := by
  have h : (w : Matrix R Q k → k) = fun m => ∑ i, ∑ j, m i j * w (Matrix.single i j 1) := by
    funext m
    conv_lhs => rw [Matrix.matrix_eq_sum_single m]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const


omit [Fintype R] [Fintype Q] in
theorem exists_cball_single {f : Matrix R Q k → ℂ} (hf : f ∈ SB (Matrix R Q k)) (e : R × Q) :
    ∃ s : kˣ, ∀ t ∈ cball s, ∀ x, f (x + Matrix.single e.1 e.2 t) = f x := by
  have hc : Continuous fun t : k => (Matrix.single e.1 e.2 t : Matrix R Q k) := by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.single, Matrix.of_apply]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have h1 : ∀ᶠ t in 𝓝 (0 : k), ∀ x ∈ tsupport f, f (x + Matrix.single e.1 e.2 t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (f (q.2 + Matrix.single e.1 e.2 q.1), f q.2) :=
      (hf.1.comp_continuous (continuous_snd.add (hc.comp continuous_fst))).prodMk
        (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + Matrix.single e.1 e.2 t ∈ tsupport f
  · have := hs (neg_mem_cball ht) _ hx'
    rw [← this, add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

def ballGrp (s : kˣ) : AddSubgroup k where
  carrier := cball s
  add_mem' := add_mem_cball
  zero_mem' := by simp [cball]
  neg_mem' := neg_mem_cball

theorem isLocallyConstant_mk (s : kˣ) : IsLocallyConstant (QuotientAddGroup.mk : k → k ⧸ ballGrp s) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' cball s ∈ 𝓝 x :=
    ((isOpen_cball s).preimage (by fun_prop)).mem_nhds (by simp [cball])
  filter_upwards [this] with z hz
  exact (QuotientAddGroup.eq.mpr hz).symm

theorem exists_sep {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (s : kˣ) {d : k} (hd : d ∉ cball s) :
    ∃ b : k, ψ (b * d) ≠ 1 ∧ ∀ u ∈ cball s, ψ (b * u) = 1 := by
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := d) (by
    rwa [show c * (c * s⁻¹)⁻¹ = s by rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]])
  refine ⟨t, hne, fun u hu => h.eq_one ?_⟩
  have h1 : valuation k t ≤ valuation k ((c * s⁻¹ : kˣ) : k) := ht
  have h2 : valuation k u ≤ valuation k (s : k) := hu
  show valuation k (t * u) ≤ valuation k (c : k)
  have h3 : (c : k) = ((c * s⁻¹ : kˣ) : k) * s := by simp
  rw [h3, map_mul, map_mul]
  exact mul_le_mul' h1 h2

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_red {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) {Φ : Matrix R Q k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R Q k)) (x : Matrix R Q k) :
    Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ))
      (Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hf : Continuous (fillAt β E I x) := by
    refine continuous_matrix fun r q => ?_
    simp only [fillAt, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hp : Continuous fun (m : Matrix R Q k) (i : I) => m i.1.1 i.1.2 :=
    continuous_pi fun i => continuous_id.matrix_elem _ _
  have h1 : HasCompactSupport fun y : I → k => Φ (fillAt β E I x y) := by
    refine HasCompactSupport.intro (IsCompact.image hΦ.2 hp) fun y hy => ?_
    refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ?_⟩
    funext i
    simp [fillAt]
  refine Continuous.integrable_of_hasCompactSupport ?_ h1.mul_right
  exact (hΦ.1.continuous.comp hf).mul
    (continuous_subtype_val.comp (hψ.comp ((continuous_form w).comp hf).neg))

theorem kills_insert_of_evalLaw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν R Q _ _ _ _ M _ _ L w β E I e hI hK hL
  classical
  by_cases hE : e ∈ E
  · rwa [Finset.insert_eq_of_mem hE]
  intro Φ hΦ
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hψ1
  obtain ⟨s₁, hs₁⟩ := exists_cball_single Φ.2 e
  have hn : (fun u : k => u * w (Matrix.single e.1 e.2 1)) ⁻¹' cball c ∈ 𝓝 (0 : k) :=
    ((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])
  obtain ⟨s, hs⟩ := exists_cball_subset (Filter.inter_mem (cball_mem_nhds s₁) hn)

  have hinv : ∀ u ∈ cball s, ∀ x, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x := by
    intro u hu x
    unfold red
    congr 1
    funext y
    have h1 : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [fillAt_add_single β hE hI, hs₁ u (hs hu).1, map_add (f := _), neg_add, AddChar.map_add_eq_mul, h1,
      hc.eq_one (neg_mem_cball (hs hu).2), mul_one]
  let p : Matrix R Q k → k ⧸ ballGrp s := fun x => QuotientAddGroup.mk (x e.1 e.2)
  have hp : IsLocallyConstant p := (isLocallyConstant_mk s).comp_continuous (continuous_id.matrix_elem _ _)
  let P : k ⧸ ballGrp s → SB (Matrix R Q k) := fun q =>
    ⟨fun x => (if p x = q then 1 else 0) * Φ.1 x,
      (hp.comp fun a => if a = q then (1 : ℂ) else 0).mul Φ.2.1, Φ.2.2.mul_left⟩
  have hred : ∀ q x, red ψ ν w β E I (P q).1 x = (if p x = q then 1 else 0) * red ψ ν w β E I Φ.1 x := by
    intro q x
    unfold red
    rw [← integral_const_mul]
    congr 1
    funext y
    simp [P, p, fillAt_apply_of_notMem β hE hI, mul_assoc]
  have hP : ∀ q, L (P q) = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    by_cases ha : a - β e.1 e.2 ∈ cball s
    · refine hK _ (funext fun x => ?_)
      rw [hred]
      split_ifs with hx
      · have h1 : -x e.1 e.2 + a ∈ cball s := QuotientAddGroup.eq.mp hx
        have h2 : β e.1 e.2 - x e.1 e.2 ∈ cball s := by
          have := add_mem_cball h1 (neg_mem_cball ha)
          convert this using 1
          ring
        have h3 := congrFun hΦ x
        rw [← hinv _ h2, one_mul]
        simpa only [red, fillAt_insert β hE hI] using h3
      · simp
    · obtain ⟨b, hb, hb'⟩ := exists_sep hc s ha
      obtain ⟨Φ', h1, h2⟩ := hL b (P a)
      set z : ℂ := (ψ (b * (a - β e.1 e.2)) : ℂ) with hz
      have h3 : L (Φ' - z • P a) = 0 := by
        refine hK _ (funext fun x => ?_)
        have h4 : red ψ ν w β E I (Φ' - z • P a).1 x =
            red ψ ν w β E I Φ'.1 x - z * red ψ ν w β E I (P a).1 x := by
          unfold red
          rw [← integral_const_mul, ← integral_sub (integrable_red hψ ν w β E I Φ'.2 x)
            ((integrable_red hψ ν w β E I (P a).2 x).const_mul z)]
          congr 1
          funext y
          change (Φ'.1 (fillAt β E I x y) - z * (P a).1 (fillAt β E I x y)) * _ = _
          ring
        rw [h4, h2, hred]
        split_ifs with hx
        · have h5 : -a + x e.1 e.2 ∈ cball s := QuotientAddGroup.eq.mp hx.symm
          have h6 : b * (x e.1 e.2 - β e.1 e.2) = b * (a - β e.1 e.2) + b * (-a + x e.1 e.2) := by ring
          rw [h6, AddChar.map_add_eq_mul, hb' _ h5, mul_one, hz]
          simp
        · simp
      rw [map_sub, map_smul, h1] at h3
      have h7 : (1 - z) ≠ 0 := fun h => hb (Circle.ext (by rw [← hz, Circle.coe_one]; exact (sub_eq_zero.mp h).symm))
      have h8 : (1 - z) • L (P a) = 0 := by rw [sub_smul, one_smul, h3]
      exact (smul_eq_zero.mp h8).resolve_left h7
  have hfin : (p '' tsupport Φ.1).Finite := by
    letI : TopologicalSpace (k ⧸ ballGrp s) := ⊥
    haveI : DiscreteTopology (k ⧸ ballGrp s) := ⟨rfl⟩
    exact (IsCompact.image Φ.2.2 hp.continuous).finite_of_discrete
  have hsum : Φ = ∑ q ∈ hfin.toFinset, P q := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, P, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Set.Finite.mem_toFinset]
    split_ifs with hx
    · rfl
    · exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨x, h, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun q _ => hP q

end GlobalTheory.PartRedEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VAddGeOfMemProdZpow
section
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.Core.Int.ProdPrimePow

theorem vAdd_eq_count {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) :
    vAdd v x = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  have key : ∀ r : 𝓞 K, r ≠ 0 → v.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
    intro r hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]
    have := v.valuation_of_algebraMap (K := K) r
    rw [HeightOneSpectrum.intValuation_if_neg _ hr] at this
    exact this
  have hv : v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at hx
    have hb1 : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
    have ha1 : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha0
    rw [map_div₀, key a ha0, key b hb0, div_eq_mul_inv (algebraMap (𝓞 K) K a),
      ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha1)
        (FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero hb1)),
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
    congr 1; ring
  unfold vAdd
  rw [hv, WithZero.log_exp, neg_neg]

theorem vAdd_ge_of_mem_prod_zpow :
    ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [DecidableEq ι]
      (e : ι ≃ HeightOneSpectrum (𝓞 K)) (S : Finset ι) (n : ι → ℤ) (a : K),
      a ∈ (∏ w ∈ S, ((e w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(n w))) →
      ∀ w : ι, a = 0 ∨ (if w ∈ S then -(n w) else 0) ≤ vAdd (e w) a := by
  intro K _ _ ι _ e S n a ha w
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  right
  have hne : ∀ i ∈ S, ((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i)) ≠ 0 := fun i _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (e i).ne_bot)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≤
      ∏ i ∈ S, ((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i)) :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 ha
  have hmono := FractionalIdeal.count_mono K (e w)
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0) hle
  rw [FractionalIdeal.count_prod K (e w) S _ hne] at hmono
  have hterm : ∀ i ∈ S, FractionalIdeal.count K (e w)
      (((e i).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(n i))) = if w = i then -(n i) else 0 := by
    intro i _
    by_cases hwi : w = i
    · subst hwi
      rw [if_pos rfl, FractionalIdeal.count_zpow_self]
    · rw [if_neg hwi, FractionalIdeal.count_zpow,
        FractionalIdeal.count_maximal_coprime K (e w) (fun h => hwi (e.injective h).symm), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq] at hmono
  rw [vAdd_eq_count (e w) ha0]
  exact hmono

end GlobalTheory.Core.Int.ProdPrimePow
end
end

