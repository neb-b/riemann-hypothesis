module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.CbIsChainApply
section
noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

def cbFam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W) : (Σ a, Fin (l a)) → W :=
  fun p => (N ^ (p.2 : ℕ)) (y p.1)

theorem cb_pow_succ (N : W →ₗ[E] W) (i : ℕ) (x : W) : N ((N ^ i) x) = (N ^ (i + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

theorem cb_pow_pow (N : W →ₗ[E] W) (m j : ℕ) (x : W) : (N ^ m) ((N ^ j) x) = (N ^ (m + j)) x := by
  rw [← Module.End.mul_apply, ← pow_add]

theorem cb_pow_zero_of_le (N : W →ₗ[E] W) {m j : ℕ} {x : W} (h : (N ^ m) x = 0) (hj : m ≤ j) :
    (N ^ j) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show m + d = d + m from add_comm _ _, ← cb_pow_pow, h, map_zero]

theorem cb_isChain_of_fam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W)
    (hy : ∀ a, (N ^ l a) (y a) = 0) (B : Module.Basis (Σ a, Fin (l a)) E W)
    (hB : ∀ p, B p = cbFam N l y p) : IsChain N l B := by
  intro a i
  rw [hB]
  simp only [cbFam]
  rw [cb_pow_succ]
  split_ifs with h
  · rw [hB]; rfl
  · have hi := i.isLt
    rw [show (i : ℕ) + 1 = l a by omega, hy]

theorem cb_isChain_apply (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : ℕ) (hi : i < l a) :
    B ⟨a, ⟨i, hi⟩⟩ = (N ^ i) (B ⟨a, ⟨0, h0⟩⟩) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := hB a ⟨i, by omega⟩
    rw [dite_eq_left (show ((⟨i, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a from hi)] at h1
    rw [← h1, ih (by omega), cb_pow_succ]

theorem cb_isChain_apply' (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by
  obtain ⟨i, hi⟩ := i
  exact cb_isChain_apply N hB a h0 i hi

theorem cb_isChain_len (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) : (N ^ l a) (B ⟨a, ⟨0, h0⟩⟩) = 0 := by
  have h1 := hB a ⟨l a - 1, by omega⟩
  rw [dite_eq_right (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)] at h1
  rw [cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ] at h1
  rwa [show l a - 1 + 1 = l a by omega] at h1

theorem cb_eq_top (N : W →ₗ[E] W) (hN : IsNilpotent N) (S : Submodule E W)
    (hS : ∀ x ∈ S, N x ∈ S) (h : S ⊔ LinearMap.range N = ⊤) : S = ⊤ := by
  have key : ∀ k : ℕ, S ⊔ LinearMap.range (N ^ k) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]
    | succ k ih =>
      rw [eq_top_iff]
      intro w _
      have hw : w ∈ S ⊔ LinearMap.range N := h ▸ Submodule.mem_top
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨z', rfl⟩ := hz
      have hz' : z' ∈ S ⊔ LinearMap.range (N ^ k) := ih ▸ Submodule.mem_top
      obtain ⟨x2, hx2, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz'
      obtain ⟨z3, rfl⟩ := hz2
      rw [map_add (f := _)]
      apply Submodule.mem_sup.mpr
      refine ⟨x + N x2, S.add_mem hx (hS _ hx2), (N ^ (k + 1)) z3, ⟨z3, rfl⟩, ?_⟩
      rw [cb_pow_succ, add_assoc]
  obtain ⟨K, hK⟩ := hN
  have := key K
  rwa [hK, LinearMap.range_zero, sup_bot_eq] at this

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainA
section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem sigma_fin_eq_iff {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by
  constructor
  · intro h
    cases h
    simp
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

theorem chain_repr_N {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr (N z) ⟨a, i⟩ = if h : 0 < (i : ℕ) then B.repr z ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
  classical
  have key : (B.coord ⟨a, i⟩).comp N =
      if h : 0 < (i : ℕ) then B.coord ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
    apply B.ext
    rintro ⟨b, j⟩
    rw [LinearMap.comp_apply, hB]
    by_cases hi : 0 < (i : ℕ)
    · rw [dite_eq_left hi]
      by_cases hj : (j : ℕ) + 1 < l b
      · rw [dite_eq_left hj, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
          Module.Basis.repr_self_apply]
        have hiff : ((⟨b, ⟨j + 1, hj⟩⟩ : Σ a, Fin (l a)) = ⟨a, i⟩) ↔
            ((⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, ⟨i - 1, by omega⟩⟩) := by
          rw [sigma_fin_eq_iff, sigma_fin_eq_iff]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at h2 ⊢; omega⟩
        exact if_congr hiff rfl rfl
      · rw [dite_eq_right hj, map_zero, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        have := i.2
        omega
    · rw [dite_eq_right hi]
      split_ifs with hj
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg, LinearMap.zero_apply]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        omega
      · simp
  have := LinearMap.congr_fun key z
  rw [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

theorem chain_repr_Npow {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr ((N ^ m) z) ⟨a, i⟩ = if h : m ≤ (i : ℕ) then B.repr z ⟨a, ⟨i - m, by omega⟩⟩ else 0 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    by_cases h1 : m + 1 ≤ (i : ℕ)
    · rw [dite_eq_left (by omega), dite_eq_left h1, chain_repr_N hB, dite_eq_left (by simp; omega)]
      congr 2
    · rw [dite_eq_right h1]
      split_ifs with h2
      · rw [chain_repr_N hB, dite_eq_right]
        simp
        omega
      · rfl

theorem chain_repr_of_ker {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (hz : (N ^ m) z = 0) (a : ι) (i : Fin (l a))
    (hi : (i : ℕ) + m < l a) : B.repr z ⟨a, i⟩ = 0 := by
  have h := chain_repr_Npow hB m z a ⟨i + m, hi⟩
  rw [hz, map_zero, dite_eq_left (by simp)] at h
  rw [Finsupp.zero_apply] at h
  rw [h]
  congr 2
  ext
  simp

theorem chain_Npow_zero {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (b : ι) (hb : 0 < l b) (j : ℕ) :
    (N ^ j) (B ⟨b, ⟨0, hb⟩⟩) = if h : j < l b then B ⟨b, ⟨j, h⟩⟩ else 0 := by
  induction j with
  | zero => simp [hb]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hj : j < l b
    · rw [dite_eq_left hj, hB]
    · rw [dite_eq_right hj, map_zero, dite_eq_right (by omega)]

theorem repr_centralizer_eq_zero (N : W →ₗ[E] W) {ι : Type} [Fintype ι] (l : ι → ℕ)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (s : ι → ℕ) (_hs : ∀ a, s a ≤ l a)
    (hC : ∀ a b, s a ≤ s b + (l a - l b)) (v : W) (hv : v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0)
    (A : W →ₗ[E] W) (hA : A ∘ₗ N = N ∘ₗ A) (a : ι) (i : Fin (l a)) (hi : (i : ℕ) < s a) :
    B.repr (A v) ⟨a, i⟩ = 0 := by
  have hc : Commute A N := hA
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hv, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : s b < l b
  · rw [dite_eq_left hb]
    have hlb : 0 < l b := by omega
    have h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩) := by
      rw [chain_Npow_zero hB b hlb, dite_eq_left hb]
    have hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x) := fun m x =>
      LinearMap.congr_fun (hc.pow_right m).eq x
    rw [h1, hcomm, chain_repr_Npow hB]
    split_ifs with h2
    · refine chain_repr_of_ker hB (l b) _ ?_ a _ ?_
      · rw [← hcomm, chain_Npow_zero hB b hlb, dite_eq_right (lt_irrefl _), map_zero]
      · have := hC a b
        show (i : ℕ) - s b + l b < l a
        omega
    · rfl
  · rw [dite_eq_right hb, map_zero, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs
section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}

theorem Frame.card_index {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    Fintype.card (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) = n := by
  rw [← Module.finrank_eq_card_basis F.β, Module.finrank_fin_fun]

theorem Frame.l_le [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) (a : F.ι m) : F.l m a ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun i : Fin (F.l m a) =>
      (⟨m, (p, ⟨a, i⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro i j h
    have h1 := sigma_mk_injective h
    have h2 := sigma_mk_injective (Prod.ext_iff.mp h1).2
    exact h2
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, F.card_index] at this
  exact this

theorem Frame.card_le [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) : Nat.card (F.ι m) ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun a : F.ι m =>
      (⟨m, (p, ⟨a, ⟨0, F.hl m a⟩⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro a b h
    have h1 := sigma_mk_injective h
    have h2 := (Prod.ext_iff.mp h1).2
    exact congrArg Sigma.fst h2
  have := Fintype.card_le_of_injective _ hinj
  rw [F.card_index] at this
  rw [Nat.card_eq_fintype_card]
  exact this

theorem exists_equiv_ls [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) (m : M) :
    ∃ e : F₁.ι m ≃ F₂.ι m, ∀ a, F₂.l m (e a) = F₁.l m a ∧ F₂.s m (e a) = F₁.s m a := by
  have hf : ∀ c : ℕ × ℕ, Nonempty ({a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃
      {b : F₂.ι m // (F₂.l m b, F₂.s m b) = c}) := by
    intro c
    rw [← Finite.card_eq]
    by_cases hc : c.1 ≤ n ∧ c.2 ≤ n
    · have e1 : {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃ {a : F₁.ι m // F₁.l m a = c.1 ∧ F₁.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      have e2 : {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} ≃ {a : F₂.ι m // F₂.l m a = c.1 ∧ F₂.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      rw [Nat.card_congr e1, Nat.card_congr e2]
      exact h m c.1 c.2 hc.1 hc.2
    · have hE1 : IsEmpty {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₁.l_le m a, (F₁.hs m a).trans (F₁.l_le m a)⟩
      have hE2 : IsEmpty {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₂.l_le m a, (F₂.hs m a).trans (F₂.l_le m a)⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
  let e := fun c => (hf c).some
  refine ⟨Equiv.ofFiberEquiv (fun c => e c), fun a => ?_⟩
  have := Equiv.ofFiberEquiv_map (f := fun a => (F₁.l m a, F₁.s m a)) (g := fun b => (F₂.l m b, F₂.s m b))
    (fun c => e c) a
  exact Prod.ext_iff.mp this

theorem conj_of_frames [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) :
    ∃ g : GL (Fin n) k, (∀ a ∈ Z, a * g.val = g.val * a) ∧ g.val * N₁ = N₂ * g.val ∧ g.val *ᵥ v₁ = v₂ := by
  choose σ hσ using exists_equiv_ls F₁ F₂ h
  let ψ : ∀ m, (Σ a : F₁.ι m, Fin (F₁.l m a)) ≃ (Σ b : F₂.ι m, Fin (F₂.l m b)) := fun m =>
    Equiv.sigmaCongr (σ m) (fun a => finCongr (hσ m a).1.symm)
  have hψ : ∀ m (a : F₁.ι m) (i : Fin (F₁.l m a)), ψ m ⟨a, i⟩ = ⟨σ m a, Fin.cast (hσ m a).1.symm i⟩ := by
    intro m a i
    rfl
  let Φ : (Σ m, L m × (Σ a : F₁.ι m, Fin (F₁.l m a))) ≃ (Σ m, L m × (Σ b : F₂.ι m, Fin (F₂.l m b))) :=
    Equiv.sigmaCongrRight (fun m => Equiv.prodCongr (Equiv.refl _) (ψ m))
  have hΦ : ∀ m (p : L m) j, Φ ⟨m, (p, j)⟩ = ⟨m, (p, ψ m j)⟩ := fun m p j => rfl
  let g : (Fin n → k) ≃ₗ[k] (Fin n → k) := F₁.β.equiv F₂.β Φ
  have hg : ∀ j, g (F₁.β j) = F₂.β (Φ j) := fun j => Module.Basis.equiv_apply _ _ _ _
  let G : GL (Fin n) k := ⟨LinearMap.toMatrix' (g : (Fin n → k) →ₗ[k] (Fin n → k)),
    LinearMap.toMatrix' (g.symm : (Fin n → k) →ₗ[k] (Fin n → k)),
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp,
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp⟩
  have hGv : ∀ x, G.val *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x

  have hext : ∀ X Y : Matrix (Fin n) (Fin n) k, (∀ j, X *ᵥ F₁.β j = Y *ᵥ F₁.β j) → X = Y := by
    intro X Y hXY
    apply Matrix.toLin'.injective
    apply F₁.β.ext
    intro j
    simp only [Matrix.toLin'_apply]
    exact hXY j
  refine ⟨G, ?_, ?_, ?_⟩
  · intro a ha
    apply hext
    rintro ⟨m, p, j⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGv, hg, hΦ]
    have h1 := F₂.hZ ⟨a, ha⟩ m p (ψ m j)
    have h2 := F₁.hZ ⟨a, ha⟩ m p j
    simp only at h1 h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, hGv, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, hg, hΦ]
  · apply hext
    rintro ⟨m, p, a, i⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F₁.hN]
    simp only [hGv]
    rw [hg, hΦ, hψ, F₂.hN]
    simp only [Fin.val_cast]
    by_cases hi : (i : ℕ) + 1 < F₁.l m a
    · have hi2 : (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dite_eq_left hi, dite_eq_left hi2, hg, hΦ, hψ]
      rfl
    · have hi2 : ¬ (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dite_eq_right hi, dite_eq_right hi2, map_zero]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hGv, F₁.hv, F₂.hv, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp (σ m)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : F₁.s m a < F₁.l m a
    · have ha2 : F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dite_eq_left ha, dite_eq_left ha2, map_smul, hg, hΦ, hψ]
      have hc : (Fin.cast (hσ m a).1.symm ⟨F₁.s m a, ha⟩ : Fin (F₂.l m (σ m a))) = ⟨F₂.s m (σ m a), ha2⟩ :=
        Fin.ext (by simp [(hσ m a).2])
      rw [hc]
    · have ha2 : ¬ F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dite_eq_right ha, dite_eq_right ha2, map_zero]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

