module

public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneLat
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_partner (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (x : Fin n → E)
    (hxx : form σ J x x = 0) (z₀ : Fin n → E) (hz₀ : z₀ ∈ L) (hz₀x : form σ J z₀ x ≠ 0) :
    ∃ y, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hσε : σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hεL : ∀ a ∈ L, ε • a ∈ L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  let C₀ : Submodule (𝓞 E) E := L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))
  let C : FractionalIdeal (𝓞 E)⁰ E := ⟨C₀, FractionalIdeal.isFractional_of_fg (hfg.map _)⟩
  have hC : ∀ z ∈ L, form σ J z x ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hC0 : C ≠ 0 := fun e => hz₀x (by simpa [e] using hC z₀ hz₀)
  have hinv : C * C⁻¹ = 1 := mul_inv_cancel₀ hC0
  have key : ∀ t ∈ C * C⁻¹, ∃ y, form σ J y x = t ∧ ∀ c ∈ C, c • y ∈ L := fun t ht => by
    refine FractionalIdeal.mul_induction_on ht (fun a ha b hb => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := ha
      refine ⟨b • z, by rw [form_smul_left, mul_comm]; rfl, fun c hc => ?_⟩
      have := FractionalIdeal.mul_mem_mul hc hb
      rw [hinv, FractionalIdeal.mem_one_iff] at this
      obtain ⟨o, ho⟩ := this
      rw [smul_smul, ← ho, algebraMap_smul]
      exact L.smul_mem o hz
    · rintro _ _ ⟨y, rfl, hy⟩ ⟨y', rfl, hy'⟩
      exact ⟨y + y', form_add_left _ _ _ _, fun c hc => by rw [smul_add]; exact L.add_mem (hy c hc) (hy' c hc)⟩
  obtain ⟨y₁, hy₁, hy₁L⟩ := key 1 (by rw [hinv]; exact FractionalIdeal.one_mem_one _)
  obtain ⟨y₀, hy₀x, hy₀L⟩ : ∃ y₀, form σ J y₀ x = ε ∧ ∀ c ∈ C, c • y₀ ∈ L :=
    ⟨ε • y₁, by rw [form_smul_left, hy₁, mul_one], fun c hc => by rw [smul_comm]; exact hεL _ (hy₁L c hc)⟩
  have hxy₀ : form σ J x y₀ = 1 := by rw [sw, hy₀x, hσε, hεε]
  have crit : ∀ y, (∀ c ∈ C, c • y ∈ L) → ∀ z ∈ L, form σ J z y • x ∈ L := fun y hy z hz => by
    refine (hd _).2 fun z' hz' => ?_
    have := hεD _ ((hd z).1 hz _ (hy _ (hC z' hz')))
    rw [form_smul_right] at this
    rw [form_smul_left, sw z' x]
    convert this using 1
    ring
  set q := form σ J y₀ y₀ with hq
  have hqq : ε * σ q = q := (sw y₀ y₀).symm
  have hyL : ∀ c ∈ C, c • (y₀ - ((θ : E) * q) • x) ∈ L := fun c hc => by
    have := L.smul_mem θ (crit y₀ hy₀L _ (hy₀L c hc))
    rw [form_smul_left, ← algebraMap_smul E θ, smul_smul] at this
    rw [smul_sub, smul_smul]
    refine L.sub_mem (hy₀L c hc) ?_
    convert this using 2
    change _ = (θ : E) * _
    ring
  refine ⟨y₀ - ((θ : E) * q) • x, ?_, ?_, fun z hz => ⟨hyL _ (hC z hz), crit _ hyL z hz⟩⟩
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right, form_smul_right,
      hxx, hxy₀, hy₀x, ← hq, map_mul]
    linear_combination -q * hθ - σ θ * hqq
  · rw [form_sub_right, form_smul_right, hxx, hxy₀]; ring

theorem exists_max_val {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) (hfg : L.FG) (f : V →ₗ[E] E) (hf : ∃ z ∈ L, f z ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ z₀ ∈ L, f z₀ ≠ 0 ∧ ∀ w ∈ S, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f z₀) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · obtain ⟨z, hz, hz0⟩ := hf
    exact ⟨z, hz, hz0, by simp⟩
  have h1 : ∀ w : HeightOneSpectrum (𝓞 E), ∃ c ∈ L, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f c) := fun w => by
    obtain ⟨G, rfl⟩ := hfg
    obtain ⟨c, hc, hmax⟩ := (insert 0 G).exists_max_image (fun z => w.valuation E (f z)) (by simp)
    refine ⟨c, ?_, fun z hz => ?_⟩
    · rcases Finset.mem_insert.1 hc with rfl | hc
      · exact zero_mem _
      · exact Submodule.subset_span hc
    · induction hz using Submodule.span_induction with
      | mem x hx => exact hmax x (Finset.mem_insert_of_mem hx)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
      | smul a x _ hx =>
        rw [← algebraMap_smul E a, map_smul, smul_eq_mul, map_mul]
        exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans hx
  choose c hcL hc using h1
  have hc0 : ∀ w : HeightOneSpectrum (𝓞 E), 0 < w.valuation E (f (c w)) := fun w => by
    obtain ⟨z, hz, hz0⟩ := hf
    exact lt_of_lt_of_le (zero_lt_iff.2 ((map_ne_zero _).2 hz0)) (hc w z hz)
  have h2 : ∀ w w' : HeightOneSpectrum (𝓞 E), ∃ p : 𝓞 E, p ∉ w.asIdeal ∧ (w' ≠ w → p ∈ w'.asIdeal) := fun w w' => by
    by_cases e : w' = w
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd e h⟩
    · have : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
        e (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
      obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 this
      exact ⟨p, hp', fun _ => hp⟩
  choose p hp hp' using h2
  let e : HeightOneSpectrum (𝓞 E) → 𝓞 E := fun w => ∏ w' ∈ S, p w w'
  have he : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (algebraMap _ E (e w)) = 1 := fun w => by
    simp only [e, map_prod]
    exact Finset.prod_eq_one fun w' _ => (w.valuation_eq_one_iff_notMem (K := E)).2 (hp w w')
  have he' : ∀ w, ∀ w' ∈ S, w' ≠ w → w'.valuation E (algebraMap _ E (e w)) < 1 := fun w w' hw' hne =>
    (w'.valuation_lt_one_iff_mem (K := E) _).2 (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hw') (hp' w w' hne))
  have hval : ∀ w ∈ S, w.valuation E (f (∑ w' ∈ S, e w' • c w')) = w.valuation E (f (c w)) := fun w hw => by
    have t : ∀ w', f (e w' • c w') = algebraMap _ E (e w') * f (c w') := fun w' => by
      rw [← algebraMap_smul E (e w'), map_smul, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.add_sum_erase S _ hw, map_add (f := _), map_sum]
    have a1 : w.valuation E (f (e w • c w)) = w.valuation E (f (c w)) := by rw [t, map_mul, he, one_mul]
    rw [Valuation.map_add_eq_of_lt_left, a1]
    rw [a1]
    refine Valuation.map_sum_lt _ (hc0 w).ne' fun w' hw' => ?_
    rw [t, map_mul]
    calc _ ≤ w.valuation E (algebraMap _ E (e w')) * w.valuation E (f (c w)) := by
          gcongr; exact hc w _ (hcL w')
      _ < _ := mul_lt_of_lt_one_left (hc0 w) (he' w' w hw (Finset.ne_of_mem_erase hw').symm)
  refine ⟨∑ w' ∈ S, e w' • c w', L.sum_mem fun w _ => L.smul_mem _ (hcL w), fun h0 => ?_, fun w hw z hz => ?_⟩
  · have := hval w₀ hw₀
    rw [h0, map_zero] at this
    exact (hc0 w₀).ne this
  · rw [hval w hw]; exact hc w z hz

theorem exists_denom (C : Submodule (𝓞 E) E) (hfg : C.FG) (w : HeightOneSpectrum (𝓞 E))
    (hC : ∀ c ∈ C, w.valuation E c ≤ 1) : ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ ∀ c ∈ C, ∃ o : 𝓞 E, (d : E) * c = o := by
  classical
  obtain ⟨G, rfl⟩ := hfg
  have h1 : ∀ c : E, ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ (w.valuation E c ≤ 1 → ∃ o : 𝓞 E, (d : E) * c = o) := fun c => by
    by_cases hc : w.valuation E c ≤ 1
    · obtain ⟨o, ⟨d, hd⟩, e⟩ := w.exists_primeCompl_mul_eq_of_integer c hc
      exact ⟨d, hd, fun _ => ⟨o, by rw [mul_comm]; exact e⟩⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd h hc⟩
  choose d hd hd' using h1
  refine ⟨∏ c ∈ G, d c, fun hm => ?_, fun c hc => ?_⟩
  · obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
    exact hd c hc
  · induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨o, ho⟩ := hd' x (hC x (Submodule.subset_span hx))
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hx
      refine ⟨k * o, ?_⟩
      rw [hk]; push_cast; linear_combination (k : E) * ho
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by push_cast; rw [mul_add]; push_cast at ha hb; rw [ha, hb]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      refine ⟨a * b, ?_⟩
      change _ * ((a : E) * x) = (a : E) * (b : E)
      rw [← hb]
      ring

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneReal
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem frame_inv {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hn : r + s = n) {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ}
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ B : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ, B * A = 1 ∧ A * B = 1 := by
  have h1 : Aᵀ * (M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.fromBlocks_multiply]
    simp
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1
  refine ⟨(M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)))ᵀ, ?_, ?_⟩
  · have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  · have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨e, A, hA⟩ := h
  have h1 : Aᵀ * (M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.fromBlocks_multiply]
    simp
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [e])).1 h1
  rw [Matrix.mul_assoc] at h2
  exact (Matrix.isUnit_det_of_right_inverse h2).ne_zero

theorem gram_vec {m k : Type} [Fintype m] [Fintype k] (M : Matrix m m ℂ) (A : Matrix m k ℂ) (u v : k → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (A *ᵥ v) = u ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ star v := by
  have e1 : star (A *ᵥ v) = A.map star *ᵥ star v := by
    funext i; simp [Matrix.mulVec, dotProduct]
  simp only [e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem cartan_of_frame {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hn : r + s = n)
    {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ} (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ θ, IsCartan M θ ∧ θ * A = A * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) := by
  obtain ⟨B, hBA, hAB⟩ := frame_inv hn hA
  set J : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hJ
  have hJJ : J * J = 1 := by rw [hJ, Matrix.fromBlocks_multiply]; simp
  have hJt : Jᵀ = J := by rw [hJ, Matrix.fromBlocks_transpose]; simp
  have hJs : J.map star = J := by
    ext (a | a) (b | b) <;> simp [hJ, Matrix.one_apply, apply_ite]
  have hθA : A * J * B * A = A * J := by rw [Matrix.mul_assoc, hBA, Matrix.mul_one]
  have ms : ∀ {a b c : Type} [Fintype b] (X : Matrix a b ℂ) (Y : Matrix b c ℂ),
      (X * Y).map star = X.map star * Y.map star := fun X Y => Matrix.map_mul (f := starRingEnd ℂ)
  refine ⟨A * J * B, ⟨?_, ?_, fun x hx => ?_⟩, hθA⟩
  · calc A * J * B * (A * J * B) = A * (J * (B * A) * J) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.mul_one, hJJ, Matrix.mul_one, hAB]
  · calc (A * J * B)ᵀ * M * (A * J * B).map star = Bᵀ * (J * (Aᵀ * M * A.map star) * J) * B.map star := by
          simp only [Matrix.transpose_mul, ms, hJt, hJs, Matrix.mul_assoc]
      _ = Bᵀ * (Aᵀ * M * A.map star) * B.map star := by rw [hA, hJJ, Matrix.one_mul]
      _ = (A * B)ᵀ * M * (A * B).map star := by simp only [Matrix.transpose_mul, ms, Matrix.mul_assoc]
      _ = M := by
          rw [hAB, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one]
  · obtain ⟨u, rfl⟩ : ∃ u, x = A *ᵥ u := ⟨B *ᵥ x, by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]⟩
    have hu : u ≠ 0 := by rintro rfl; simp at hx
    rw [Matrix.mulVec_mulVec, hθA, ← Matrix.mulVec_mulVec, gram_vec, hA, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hJt, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
    open scoped ComplexOrder in
    exact (Complex.pos_iff.1 (Matrix.dotProduct_self_star_pos_iff.2 hu)).1

theorem hasSig_unique {n r s p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h' : HasSig M p q) :
    r = p ∧ s = q := by
  obtain ⟨e, A, hA⟩ := h
  obtain ⟨e', A', hA'⟩ := h'
  have k : ∀ {r s : ℕ} (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ), (A.map star)ᴴ = Aᵀ := fun A => by ext a b; simp
  have h1 := Formalism.UG.P.sig_dim M (A.map star) (by rw [k]; exact hA) (A'.map star) (by rw [k]; exact hA')
  have h2 := Formalism.UG.P.sig_dim M (A'.map star) (by rw [k]; exact hA') (A.map star) (by rw [k]; exact hA)
  rw [Fintype.card_fin] at h1 h2
  omega

theorem hasSig_exists {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hdet : M.det ≠ 0) : ∃ p q, HasSig M p q := by
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ M (by rw [Formalism.UG.IsHerm, Formalism.UG.P.cT_conj_eq, hM]) hdet.isUnit
  obtain ⟨e, Q, hQ⟩ := Formalism.UG.P.sig_data M p q h
  refine ⟨p, q, by simpa using e.symm, Q.map star, ?_⟩
  have : (Q.map star).map star = Q := by ext a b; simp
  rw [this]
  exact hQ

theorem herm_swap {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (u v : Fin n → ℂ) :
    v ⬝ᵥ M *ᵥ star u = star (u ⬝ᵥ M *ᵥ star v) := by
  have hM' : ∀ i j, star (M i j) = M j i := fun i j => by rw [← Matrix.conjTranspose_apply, hM]
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, hM', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem real_plane {n n₁ : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (X Y : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) {r s : ℕ} (hn : n = n₁ + 2) (hM : Mᴴ = M)
    (hXX : X ⬝ᵥ M *ᵥ star X = 0) (hYY : Y ⬝ᵥ M *ᵥ star Y = 0) (hXY : X ⬝ᵥ M *ᵥ star Y = 1)
    (hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0) (hιY : ιᵀ *ᵥ (M *ᵥ star Y) = 0) (hP : P * ι = 1) (hsig : HasSig M r s) :
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) ∧ ∃ θ θ₁, IsCartan M θ ∧ IsCartan (ιᵀ * M * ι.map star) θ₁ ∧
      θ * ι = ι * θ₁ ∧ Y = (2 : ℂ) • θ *ᵥ X := by
  classical
  have hYX : Y ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap hM, hXY, star_one]
  have oX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := fun u => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hιX, zero_dotProduct]
  have oY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0 := fun u => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hιY, zero_dotProduct]
  have oX' : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := fun u => by rw [herm_swap hM, oX, star_zero]
  have oY' : ∀ u, Y ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := fun u => by rw [herm_swap hM, oY, star_zero]
  have hinj : ∀ u, ι *ᵥ u = 0 → u = 0 := fun u hu => by
    have := congrArg (P *ᵥ ·) hu
    simpa [Matrix.mulVec_mulVec, hP] using this
  have hspan : ∀ Z : Fin n → ℂ, ∃ (a : ℂ) (u : Fin n₁ → ℂ) (b : ℂ), a • X + ι *ᵥ u + b • Y = Z := by
    let f : (ℂ × ℂ) × (Fin n₁ → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
      ((LinearMap.toSpanSingleton ℂ _ X).coprod (LinearMap.toSpanSingleton ℂ _ Y)).coprod ι.mulVecLin
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨⟨a, b⟩, u⟩ h0
      have h0' : a • X + b • Y + ι *ᵥ u = 0 := h0
      have ha : a = 0 := by
        have := congrArg (· ⬝ᵥ M *ᵥ star Y) h0'
        simpa [add_dotProduct, smul_dotProduct, hXY, hYY, oY] using this
      have hb : b = 0 := by
        have := congrArg (· ⬝ᵥ M *ᵥ star X) h0'
        simpa [add_dotProduct, smul_dotProduct, hXX, hYX, oX] using this
      subst ha hb
      rw [hinj u (by simpa using h0')]
      rfl
    intro Z
    obtain ⟨⟨⟨a, b⟩, u⟩, hZ⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f)
      (by simp [hn]; omega)).1 hf Z
    exact ⟨a, u, b, by rw [← hZ, add_right_comm]; rfl⟩
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hM₁h : M₁ᴴ = M₁ := by
    have e1 : (ι.map star)ᴴ = ιᵀ := by ext a b; simp
    have e2 : ιᵀᴴ = ι.map star := by ext a b; simp
    rw [hM₁, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, hM, Matrix.mul_assoc]
  have hdet₁ : M₁.det ≠ 0 := fun h0 => by
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M *ᵥ star (ι *ᵥ star v) = 0 := by
      funext k
      obtain ⟨a, u, b, hZ⟩ := hspan (Pi.single k 1)
      have : (a • X + ι *ᵥ u + b • Y) ⬝ᵥ M *ᵥ star (ι *ᵥ star v) = 0 := by
        rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, oX', oY', gram_vec, star_star, ← hM₁, hMv]
        simp
      rw [hZ] at this
      simpa using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero (det_ne_zero_of_hasSig hsig) h1
    exact hv (star_eq_zero.1 (hinj _ (star_eq_zero.1 h2)))
  obtain ⟨p, q, hpq, A₁, hA₁⟩ := hasSig_exists hM₁h hdet₁
  let c : Fin (p + 1) ⊕ Fin (q + 1) → Fin n → ℂ :=
    Sum.elim (Fin.cons (X + (1 / 2 : ℂ) • Y) fun a => ι *ᵥ A₁ *ᵥ Pi.single (Sum.inl a) 1)
      (Fin.cons (X - (1 / 2 : ℂ) • Y) fun a => ι *ᵥ A₁ *ᵥ Pi.single (Sum.inr a) 1)
  obtain ⟨A, hcol⟩ : ∃ A : Matrix (Fin n) (Fin (p + 1) ⊕ Fin (q + 1)) ℂ, ∀ k, A *ᵥ Pi.single k 1 = c k :=
    ⟨(Matrix.of c)ᵀ, fun k => by funext i; simp⟩
  have ent : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℂ) (a b : κ),
      Pi.single a 1 ⬝ᵥ G *ᵥ star (Pi.single b (1 : ℂ) : κ → ℂ) = G a b := fun G a b => by
    rw [← Pi.single_star]; simp
  have g1 : ∀ a b, (ι *ᵥ A₁ *ᵥ Pi.single a 1) ⬝ᵥ M *ᵥ star (ι *ᵥ A₁ *ᵥ Pi.single b 1) =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) a b := fun a b => by
    rw [gram_vec, gram_vec, ← hM₁, hA₁, ent]
  have hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1) := by
    ext a b
    rw [← ent (Aᵀ * M * A.map star), ← gram_vec, hcol, hcol]
    rcases a with a | a <;> rcases b with b | b <;> refine Fin.cases ?_ (fun a => ?_) a <;>
      refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [c, Sum.elim_inl, Sum.elim_inr, Fin.cons_zero, Fin.cons_succ, g1, add_dotProduct, sub_dotProduct,
        smul_dotProduct, star_add, star_sub, star_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
        dotProduct_add, dotProduct_sub, dotProduct_smul, oX, oY, oX', oY', hXX, hYY, hXY, hYX] <;>
      simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm] <;> norm_num
  have hn' : p + 1 + (q + 1) = n := by omega
  obtain ⟨rfl, rfl⟩ := hasSig_unique hsig ⟨hn', A, hA⟩
  obtain ⟨θ, hθ, hθA⟩ := cartan_of_frame hn' hA
  obtain ⟨θ₁, hθ₁, hθA₁⟩ := cartan_of_frame hpq hA₁
  obtain ⟨B₁, -, hAB₁⟩ := frame_inv hpq hA₁
  have jl : ∀ {r s : ℕ} (a : Fin r), (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) *ᵥ
      Pi.single (Sum.inl a) 1 = Pi.single (Sum.inl a) 1 := fun a => by
    funext k; rcases k with k | k <;> simp [Matrix.one_apply, Pi.single_apply]
  have jr : ∀ {r s : ℕ} (a : Fin s), (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) *ᵥ
      Pi.single (Sum.inr a) 1 = -Pi.single (Sum.inr a) 1 := fun a => by
    funext k; rcases k with k | k <;> simp [Matrix.one_apply, Pi.single_apply]
  have tl : ∀ a, θ *ᵥ c (Sum.inl a) = c (Sum.inl a) := fun a => by
    rw [← hcol, Matrix.mulVec_mulVec, hθA, ← Matrix.mulVec_mulVec, jl]
  have tr : ∀ a, θ *ᵥ c (Sum.inr a) = -c (Sum.inr a) := fun a => by
    rw [← hcol, Matrix.mulVec_mulVec, hθA, ← Matrix.mulVec_mulVec, jr, Matrix.mulVec_neg]
  refine ⟨⟨hpq, A₁, hA₁⟩, θ, θ₁, hθ, hθ₁, ?_, ?_⟩
  · have : θ * ι * A₁ = ι * θ₁ * A₁ := by
      rw [Matrix.mul_assoc ι, hθA₁]
      refine Matrix.ext_of_mulVec_single fun k => ?_
      simp only [← Matrix.mulVec_mulVec]
      rcases k with k | k
      · rw [jl]; exact tl k.succ
      · rw [jr, Matrix.mulVec_neg, Matrix.mulVec_neg]; exact tr k.succ
    rw [← Matrix.mul_one (θ * ι), ← hAB₁, ← Matrix.mul_assoc, this, Matrix.mul_assoc, hAB₁, Matrix.mul_one]
  · have a1 : θ *ᵥ (X + (1 / 2 : ℂ) • Y) = X + (1 / 2 : ℂ) • Y := tl 0
    have a2 : θ *ᵥ (X - (1 / 2 : ℂ) • Y) = -(X - (1 / 2 : ℂ) • Y) := tr 0
    rw [Matrix.mulVec_add] at a1
    rw [Matrix.mulVec_sub] at a2
    funext i
    have b1 := congrFun a1 i
    have b2 := congrFun a2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at b1 b2 ⊢
    linear_combination -b1 - b2

end PositivityTheory.ThKG.Tow.Pln

end
end

