module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.ExistsRefl
section
namespace PositivityTheory.ThKG.Tow.Levi

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def hf (M : Matrix n n ℂ) : (n → ℂ) →ₗ[ℂ] (n → ℂ) →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x ⬝ᵥ M *ᵥ star y)
    (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => smul_dotProduct _ _ _)
    (fun _ _ _ => by rw [star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [star_smul, mulVec_smul, dotProduct_smul]; rfl)

variable {M θ : Matrix n n ℂ}

omit [DecidableEq n] in
theorem hf_apply (x y : n → ℂ) : hf M x y = x ⬝ᵥ M *ᵥ star y := rfl

omit [DecidableEq n] in
theorem hf_mulVec (g : Matrix n n ℂ) (x y : n → ℂ) : hf M (g *ᵥ x) (g *ᵥ y) = hf (gᵀ * M * g.map star) x y := by
  have e : star (g *ᵥ y) = g.map star *ᵥ star y := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) g y i
  rw [hf_apply, hf_apply, e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

theorem iso_of_hf {g : Matrix n n ℂ} (h : ∀ x y, hf M (g *ᵥ x) (g *ᵥ y) = hf M x y) : gᵀ * M * g.map star = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_mulVec, hf_apply, hf_apply] at this
  simpa [← Pi.single_star] using this

omit [DecidableEq n] in
theorem hf_conj (hM : ∀ i j, star (M j i) = M i j) (x y : n → ℂ) : starRingEnd ℂ (hf M x y) = hf M y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf_apply, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hM i j]
  simp [mul_comm, mul_left_comm]

theorem exists_refl (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {u u' : n → ℂ}
    (hu : θ *ᵥ u = ε • u) (hu' : θ *ᵥ u' = ε • u') (e : hf M u u = hf M u' u') :
    ∃ κ : Matrix n n ℂ, κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ u = u' ∧ ∀ z, θ *ᵥ z = -ε • z → κ *ᵥ z = z := by
  obtain ⟨a, ha⟩ : ∃ a, a = u - u' := ⟨_, rfl⟩
  have hθ : ∀ x y, hf M (θ *ᵥ x) (θ *ᵥ y) = hf M x y := fun x y => by rw [hf_mulVec, h2]
  have hθθ : ∀ x, θ *ᵥ (θ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h1, one_mulVec]
  have hεc : starRingEnd ℂ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hθa : θ *ᵥ a = ε • a := by rw [ha, mulVec_sub, hu, hu', smul_sub]
  have haa : hf M a a = hf M u a + starRingEnd ℂ (hf M u a) := by
    rw [hf_conj hM, ha]
    simp only [map_sub, LinearMap.sub_apply]
    rw [e]; ring
  obtain ⟨b, hb⟩ : ∃ b, b = hf M u a := ⟨_, rfl⟩
  rw [← hb] at haa
  let κ : Matrix n n ℂ := 1 - b⁻¹ • vecMulVec a (M *ᵥ star a)
  have hκ : ∀ z, κ *ᵥ z = z - (b⁻¹ * hf M z a) • a := fun z => by
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hf_apply, dotProduct_comm z]
    simp [mul_smul]
  refine ⟨κ, iso_of_hf fun z w => ?_, ?_, ?_, fun z hz => ?_⟩
  · rw [hκ, hκ]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, haa,
      map_mul, map_inv₀, hf_conj hM]
    by_cases h0 : b = 0
    · simp [h0]
    · have h0' : starRingEnd ℂ b ≠ 0 := by simpa using h0
      field_simp
      ring
  · refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    have : hf M (θ *ᵥ z) a = ε * hf M z a := by
      rw [← hθ, hθθ, hθa, LinearMap.map_smulₛₗ, hεc, smul_eq_mul]
    rw [toLin'_apply, toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, hκ, hκ, mulVec_sub, mulVec_smul, hθa, this, smul_smul]
    congr 2
    ring
  · rw [hκ, ← hb]
    by_cases h0 : b = 0
    · have : a = 0 := by
        by_contra hne
        have := h3 a hne
        rw [hθa, map_smul, LinearMap.smul_apply, haa, h0] at this
        simp at this
      rw [this, smul_zero, sub_zero]
      exact sub_eq_zero.1 (ha ▸ this)
    · rw [inv_mul_cancel₀ h0, one_smul, ha, sub_sub_cancel]
  · have : hf M z a = 0 := by
      have := hθ z a
      rw [hz, hθa, LinearMap.map_smulₛₗ, hεc, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
      linear_combination (-1 / 2 : ℂ) * this - (1 / 2 : ℂ) * hf M z a * hεε
    rw [hκ, this, mul_zero, zero_smul, sub_zero]

theorem exists_move (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {v v' : n → ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (e : hf M v v = 0) (e' : hf M v' v' = 0) :
    ∃ (κ : Matrix n n ℂ) (t : ℂ), t ≠ 0 ∧ κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ v = t • v' := by
  have hθ : ∀ x y, hf M (θ *ᵥ x) (θ *ᵥ y) = hf M x y := fun x y => by rw [hf_mulVec, h2]
  have hθθ : ∀ x, θ *ᵥ (θ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h1, one_mulVec]
  have hs : ∀ x, hf M x (θ *ᵥ x) = hf M (θ *ᵥ x) x := fun x => by rw [← hθ, hθθ]
  have hre : ∀ x, ((hf M (θ *ᵥ x) x).re : ℂ) = hf M (θ *ᵥ x) x := fun x =>
    Complex.conj_eq_iff_re.1 (by rw [hf_conj hM, hs])
  have p := h3 v hv
  have p' := h3 v' hv'
  let t : ℝ := Real.sqrt ((hf M (θ *ᵥ v) v).re / (hf M (θ *ᵥ v') v').re)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos p p')
  have htt : (t : ℂ) * t * hf M (θ *ᵥ v') v' = hf M (θ *ᵥ v) v := by
    rw [← hre v, ← hre v', ← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (div_pos p p').le,
      div_mul_cancel₀ _ p'.ne']
  obtain ⟨w, hw⟩ : ∃ w, w = (t : ℂ) • v' := ⟨_, rfl⟩
  have ew : hf M w w = 0 := by
    rw [hw, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, e', smul_zero, smul_zero]
  have ew' : hf M (θ *ᵥ w) w = hf M (θ *ᵥ v) v := by
    rw [hw, LinearMap.map_smulₛₗ, mulVec_smul, map_smul, LinearMap.smul_apply, Complex.conj_ofReal, ← htt, smul_eq_mul,
      smul_eq_mul, mul_assoc]
  have ep : ∀ x, θ *ᵥ (x + θ *ᵥ x) = (1 : ℂ) • (x + θ *ᵥ x) := fun x => by rw [mulVec_add, hθθ, one_smul, add_comm]
  have em : ∀ x, θ *ᵥ (x - θ *ᵥ x) = (-1 : ℂ) • (x - θ *ᵥ x) := fun x => by rw [mulVec_sub, hθθ, neg_one_smul, neg_sub]
  obtain ⟨κ₁, a1, a2, a3, a4⟩ := exists_refl hM h1 h2 h3 (Or.inl rfl) (ep v) (ep w) (by
    simp only [map_add (f := _), LinearMap.add_apply, hθ, hs, e, ew, ew'])
  obtain ⟨κ₂, b1, b2, b3, b4⟩ := exists_refl hM h1 h2 h3 (Or.inr rfl) (em v) (em w) (by
    simp only [map_sub, LinearMap.sub_apply, hθ, hs, e, ew, ew'])
  refine ⟨κ₂ * κ₁, t, by exact_mod_cast ht.ne', iso_of_hf fun x y => ?_, b2.mul_left a2, ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hf_mulVec, b1, hf_mulVec, a1]
  · have e1 : v = (2 : ℂ)⁻¹ • ((v + θ *ᵥ v) + (v - θ *ᵥ v)) := by module
    rw [← hw, ← mulVec_mulVec, e1, mulVec_smul, mulVec_add, a3, a4 _ (em v), mulVec_smul, mulVec_add, b3,
      b4 _ (by rw [neg_neg]; exact ep w)]
    module

end PositivityTheory.ThKG.Tow.Levi
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.LeviAlg
section
namespace PositivityTheory.ThKG.Tow.Levi

open Matrix

variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

def fr (ι : Matrix d e R) (x y : d → R) : Matrix d (e ⊕ Fin 2) R := fromCols ι (of fun i j => ![x i, y i] j)

def gr (J₁ : Matrix e e R) : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks J₁ 0 0 !![0, 1; -1, 0]

structure IsFr (c : R →+* R) (J : Matrix d d R) (J₁ : Matrix e e R) (ι : Matrix d e R) (x y : d → R) : Prop where
  gram : (fr ι x y)ᵀ * J * (fr ι x y).map c = gr J₁
  inv : ∃ A' : Matrix (e ⊕ Fin 2) d R, fr ι x y * A' = 1 ∧ A' * fr ι x y = 1

variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem fr_map (f : R →+* S) : fr (ι.map f) (fun i => f (x i)) (fun i => f (y i)) = (fr ι x y).map f := by
  ext i (j | j)
  · rfl
  · fin_cases j <;> rfl

omit [Fintype e] [DecidableEq e] in
theorem gr_map (f : R →+* S) : gr (J₁.map f) = (gr J₁).map f := by
  ext (i | i) (j | j)
  · rfl
  · simp [gr]
  · simp [gr]
  · fin_cases i <;> fin_cases j <;> simp [gr]

theorem IsFr.map (h : IsFr c J J₁ ι x y) (f : R →+* S) {c' : S →+* S} (hc : ∀ a, f (c a) = c' (f a)) :
    IsFr c' (J.map f) (J₁.map f) (ι.map f) (fun i => f (x i)) (fun i => f (y i)) := by
  obtain ⟨hg, A', h1, h2⟩ := h
  refine ⟨?_, A'.map f, ?_, ?_⟩
  · rw [fr_map, gr_map, ← hg, Matrix.map_mul, Matrix.map_mul]
    congr 1
    exact Matrix.ext fun i j => (hc _).symm
  · rw [fr_map, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [fr_map, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem IsFr.isUnit_det (h : IsFr c J J₁ ι x y) (hJ : IsUnit J.det) : IsUnit J₁.det := by
  obtain ⟨hg, A', h1, h2⟩ := h
  have e1 : (fr ι x y).map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : gr J₁ * (A'.map c * J⁻¹ * A'ᵀ) = 1 := by
    rw [← hg]
    calc _ = (fr ι x y)ᵀ * (J * ((fr ι x y).map c * A'.map c) * J⁻¹) * A'ᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, mul_nonsing_inv _ hJ, Matrix.mul_one, ← transpose_mul, h2, transpose_one]
  have e3 := Matrix.isUnit_det_of_right_inverse e2
  rw [gr, det_fromBlocks_zero₂₁] at e3
  exact isUnit_of_mul_isUnit_left e3

omit [DecidableEq d] [DecidableEq e] in
theorem cols_of_mul {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by
  rw [fr, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff] at h
  refine ⟨h.1, funext fun i => ?_, funext fun i => ?_⟩
  · have := congrFun (congrFun h.2 i) 0
    simpa [Matrix.mul_apply, mulVec, dotProduct, add_assoc, mul_comm] using this
  · have := congrFun (congrFun h.2 i) 1
    simpa [Matrix.mul_apply, mulVec, dotProduct, add_assoc, mul_comm] using this

theorem IsFr.levi (h : IsFr c J J₁ ι x y) (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by
  obtain ⟨hG, A', h1, h2⟩ := h
  set A := fr ι x y with hA
  let D : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g 0 0 !![t, 0; 0, c t']
  let D' : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g' 0 0 !![t', 0; 0, c t]
  have hct : c t' * c t = 1 := by rw [← map_mul, mul_comm, ht, map_one]
  have hD : D * D' = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simpa using hg'
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ht, hct]
  have hDG : Dᵀ * gr J₁ * D.map c = gr J₁ := by
    rw [gr, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    · simpa using hg
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, ht, hct, hcc]
  have e1 : A.map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : A * D * A' * A = A * D := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  obtain ⟨c1, c2, c3⟩ := cols_of_mul e2
  refine ⟨A * D * A', A * D' * A', ?_, ?_, ?_, ?_, ?_⟩
  · calc _ = A * (D * (A' * A) * D') * A' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hD, Matrix.mul_one, h1]
  · calc _ = A'ᵀ * (Dᵀ * (Aᵀ * J * A.map c) * D.map c) * A'.map c := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = (A * A')ᵀ * J * (A.map c * A'.map c) := by
          rw [hG, hDG, ← hG]; simp only [transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · rw [c2]; ext i; simp [mulVec, dotProduct]
  · rw [c3]; ext i; simp [mulVec, dotProduct]
  · simpa using c1

theorem IsFr.stab (h : IsFr c J J₁ ι x y) {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by
  obtain ⟨hG, A', h1, h2⟩ := h
  set A := fr ι x y with hA
  have hP : (A' * p * A)ᵀ * gr J₁ * (A' * p * A).map c = gr J₁ := by
    have e1 : A.map c * A'.map c = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hG]
    calc _ = Aᵀ * (pᵀ * ((A * A')ᵀ * J * (A.map c * A'.map c)) * p.map c) * A.map c := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one, hp]
  have e2 : p * A = A * (A' * p * A) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e3 : ∀ i, (A' * p * A) i (Sum.inr 0) = t * (1 : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R) i (Sum.inr 0) := fun i => by
    rw [← h2, Matrix.mul_assoc]
    change (A' *ᵥ (p *ᵥ x)) i = t * (A' *ᵥ x) i
    rw [hx, mulVec_smul]; rfl
  generalize A' * p * A = P at hP e2 e3
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  have e4 : ∀ j, P (Sum.inr 1) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP (Sum.inl j)) (Sum.inr 0)
    simp [Matrix.mul_apply, e3, gr, one_apply, Fintype.sum_sum_type, apply_ite c] at this
    calc _ = P (Sum.inr 1) (Sum.inl j) * c t * c t' := by rw [mul_assoc, hct, mul_one]
      _ = 0 := by rw [this, zero_mul]
  rw [← fromBlocks_toBlocks P] at e2
  refine ⟨P.toBlocks₁₁, fun j => P (Sum.inr 0) (Sum.inl j), ?_, fun z => ?_⟩
  · ext i j
    have := congrFun (congrFun hP (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, e4, gr, Fintype.sum_sum_type, toBlocks₁₁] using this
  · rw [mulVec_mulVec, (cols_of_mul e2).1, add_mulVec, mulVec_mulVec]
    congr 1
    ext i
    simp [mulVec, dotProduct, Matrix.mul_apply, toBlocks₂₁, e4, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm]

end PositivityTheory.ThKG.Tow.Levi
end

